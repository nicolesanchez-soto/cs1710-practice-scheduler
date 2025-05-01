#lang forge/temporal

open "basic_model.frg"


// test statements from a focus group of what they'd want from a model 
pred noEmptyPieces {
    all p: Piece | some d: Dancer | p in d.assignments
}

pred everyoneInAtLeastOnePiece {
    eventually (all d: Dancer | some d.assignments)
}

pred pieceInOnePrefTierOnly {
    all d: Dancer {
        no (d.mustHavePreferences & d.preferences & d.avoidPreferences)
    }
}

pred allDancesHaveRehearsalTime {
    all p: Piece | some p.rehearsalSlots
}

// pred noPiecesAboveMaximum {

// }

// pred dancerIsNotInTwoPlacesAtOnce {

// }

// pred noPiecesBelowMinimum {
//     ...
// }




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



test suite for validAssignment {
    assert noEmptyPieces is necessary for validAssignment
    assert everyoneInAtLeastOnePiece is necessary for validAssignment
    assert allDancesHaveRehearsalTime is necessary for validAssignment
    assert pieceInOnePrefTierOnly is necessary for validAssignment
    
    test expect {noDancerInternalConflict: {validAssignment and dancerHasInternalConflict} is unsat}
    test expect {noDancerExternalConflict: {validAssignment and dancerHasExternalConflict} is unsat}
}