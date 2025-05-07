#lang forge/temporal

open "with_preferences.frg"


// Google Forms automatically enforces/implies this for you
pred pieceInOnePrefTierOnly {
    all d: Dancer {
        no (d.mustHavePreferences & d.preferences & d.avoidPreferences)
    }
}

test suite for init {
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