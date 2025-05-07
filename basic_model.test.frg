#lang forge/temporal

open "basic_model.frg"


// test statements from a focus group of what they'd want to see from this model 
pred noEmptyPieces {
    all p: Piece | some d: Dancer | p in d.assignments
}

pred everyoneInAtLeastOnePiece {
    eventually (all d: Dancer | some d.assignments)
}

pred dancerHasInternalConflict {
    // There's some dancer, and two separate pieces...
    some d: Dancer | some disj p1, p2: Piece | {
        // .. that have timeslots for the same time...
        some (p1.rehearsalSlots & p2.rehearsalSlots) and
        // but the dancer is assigned to both pieces!
        p1 in d.assignments and
        p2 in d.assignments
    } 
}

pred dancerHasExternalConflict {
    // There's some dancer, and some timeslot, and some piece
    some d: Dancer | some ts: TimeSlot | some p: Piece {
        // ... where a piece is assigned to a dancer...
        p in d.assignments and
        // ... and there's a timeslot given to that piece...
        ts in p.rehearsalSlots and 
        // ... but the dancer isn't available for that time!
        ts not in d.availability 
    }
}


test suite for validAssignment {
    // testing most common concerns!
    assert noEmptyPieces is necessary for validAssignment
    assert everyoneInAtLeastOnePiece is necessary for validAssignment
    
    test expect {noDancerInternalConflict: {validAssignment and dancerHasInternalConflict} is unsat}
    test expect {noDancerExternalConflict: {validAssignment and dancerHasExternalConflict} is unsat}
}

// Google Forms automatically enforces/implies these for you
pred pieceInOnePrefTierOnly {
    all d: Dancer {
        no (d.mustHavePreferences & d.preferences & d.avoidPreferences)
    }
}

pred allPiecesHaveRehearsalTime {
    all p: Piece | some p.rehearsalSlots
}


test suite for init {
    assert allPiecesHaveRehearsalTime is necessary for init
    assert pieceInOnePrefTierOnly is necessary for init   
}

pred dancerIsNeverAvailable {
    some d: Dancer {
        no d.availability implies no d.assignments
    }
}

pred assignedToAvoidedPieceDueToNecessity {
    #Dancer = 3
    some d: Dancer, p: Piece | {
        p.minDancers >= 2
        // Dancer is assigned to a piece they wanted to avoid
        p in d.assignments and p in d.avoidPreferences
    
        // Dancer is available at that piece’s times
        p.rehearsalSlots in d.availability

        // No other dancer is available despite not avoiding the piece
        no d2: Dancer - d | {
            p.rehearsalSlots in d2.availability
            p not in d2.avoidPreferences
        }
  }
}

pred mustHaveNeverSatisfied {
    always {
        some d: Dancer | {
            some d.mustHavePreferences
            no (d.assignments & d.mustHavePreferences)
        }
    }
}

pred popularPieceGoesUnassigned {
    some p: Piece | {
        some d: Dancer | p in d.mustHavePreferences + d.preferences
        no d: Dancer | p in d.assignments
    }
}

pred allAvoidEverything {
    all d: Dancer, p: Piece | p in d.avoidPreferences
}

pred oneDancerWantsEveryPiece {
    // some non-trivial amount of pieces to represent an extreme case
    #Piece >= 5
    some d: Dancer | d.mustHavePreferences = Piece
}

// exploring preference vs. assignment possibilities!
test suite for eventuallyValidTrace {
    test expect {aDancerWithNoAvailabity: {dancerIsNeverAvailable and eventuallyValidTrace} is sat}
    test expect {popPieceUnassigned: {popularPieceGoesUnassigned and eventuallyValidTrace} is sat}

    // fails! in real life, it's possible to be in these situations but the model doesn't allow it (interestingly)
    // test expect {unfortunateSituation1: {assignedToAvoidedPieceDueToNecessity and eventuallyValidTrace} is sat}
    // test expect {unfortunateSituation2: {mustHaveNeverSatisfied and eventuallyValidTrace} is sat}


    test expect {everyoneAvoids: {allAvoidEverything and eventuallyValidTrace} is unsat}

    // it's interesting that there's just no trace that sees a dancer just not get what they want?
    test expect {dancerWantsToBeInEverything: {oneDancerWantsEveryPiece and eventuallyValidTrace} is unsat}

}

