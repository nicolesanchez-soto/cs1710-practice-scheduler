#lang forge/temporal

open "basic_model.frg"


// test statements from a focus group of what they'd want to see from this model 
pred noEmptyPieces {
    all p: Piece | some d: Dancer | p in d.assignments
}

pred everyoneInAtLeastOnePiece {
    eventually (all d: Dancer | some d.assignments)
}


// Google Sheets automatically enforces this for you
pred pieceInOnePrefTierOnly {
    all d: Dancer {
        no (d.mustHavePreferences & d.preferences & d.avoidPreferences)
    }
}

pred allPiecesHaveRehearsalTime {
    all p: Piece | some p.rehearsalSlots
}


// test unsatisfactory scenarios cannot be produced by this model
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

pred oneDancerWantsEveryPiece {
    // some non-trivial amount of pieces to represent an extreme case
    #Piece >= 3
    some d: Dancer | d.mustHavePreferences = Piece
}

test suite for validAssignment {
    // testing most common concerns!
    assert noEmptyPieces is necessary for validAssignment
    assert everyoneInAtLeastOnePiece is necessary for validAssignment
    assert allPiecesHaveRehearsalTime is necessary for validAssignment
    assert pieceInOnePrefTierOnly is necessary for validAssignment
    
    test expect {noDancerInternalConflict: {validAssignment and dancerHasInternalConflict} is unsat}
    test expect {noDancerExternalConflict: {validAssignment and dancerHasExternalConflict} is unsat}


    // testing for edge cases
    // save for preference testing
    // test expect {dancerWantsToBeInEverything: {validAssignment and oneDancerWantsEveryPiece} is unsat}
}

