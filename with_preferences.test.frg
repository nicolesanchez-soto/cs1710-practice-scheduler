#lang forge/temporal

open "with_preferences.frg"


// Google Forms automatically enforces/implies this for you
pred pieceInOnePrefTierOnly {
    all d: Dancer {
        no (d.mustHavePreferences & d.preferences)
        no (d.preferences & d.avoidPreferences)
        no (d.mustHavePreferences & d.avoidPreferences)
    }
}

// in real life, dancers shouldn't mark pieces as preferred if they can't attend those rehearsals
pred preferencesMatchAvailability {
    all d: Dancer, p: Piece | {
        (p in d.mustHavePreferences or p in d.preferences) implies
        p.rehearsalSlots in d.availability
    }
}

test suite for init {
    assert pieceInOnePrefTierOnly is necessary for init   
}

// dancer is never available for any rehearsal slots, basic model test
pred dancerIsNeverAvailable {
    some d: Dancer {
        no d.availability implies no d.assignments
    }
}

// tests for example where a dancer is assigned to a piece they wanted to avoid (should never happen)
pred assignedToAvoidedPieceDueToNecessity {
    #Dancer = 3
    some d: Dancer, p: Piece | {
        p.minDancers >= 2
        // dancer is assigned to a piece they wanted to avoid
        p in d.assignments and p in d.avoidPreferences
    
        // dancer is available at that piece’s times
        p.rehearsalSlots in d.availability

        // no other dancer is available despite not avoiding the piece
        no d2: Dancer - d | {
            p.rehearsalSlots in d2.availability
            p not in d2.avoidPreferences
        }
  }
}

// tests for case where dancer doesn't get their must-have
pred mustHaveNeverSatisfied {
    always {
        some d: Dancer | {
            some d.mustHavePreferences
            no (d.assignments & d.mustHavePreferences)
        }
    }
}

// a piece that is popular but no one can be assigned to it
pred popularPieceGoesUnassigned {
    some p: Piece | {
        some d: Dancer | p in d.mustHavePreferences + d.preferences
        no d: Dancer | p in d.assignments
    }
}

// a dancer that doesn't want to be in any piece
pred allAvoidEverything {
    all d: Dancer, p: Piece | p in d.avoidPreferences
}

// some extreme case where a dancer wants to be in every piece
pred oneDancerWantsEveryPiece {
    // some non-trivial amount of pieces to represent an extreme case
    #Piece >= 5
    some d: Dancer | d.mustHavePreferences = Piece
}

// tests that preferences are evenly distributed
pred evenPreferenceDistribution {
    // every piece is someone's preference
    all p: Piece | some d: Dancer | 
        p in d.mustHavePreferences or p in d.preferences
    
    // and preferences are evenly distributed
    let avgPrefsPerDancer = divide[multiply[#Piece, #Dancer], #Dancer] |
    all d: Dancer | 
        abs[(#(d.mustHavePreferences + d.preferences)) - avgPrefsPerDancer] <= 1
}

// makes sure score is calculated correctly
pred satisfactionScoreCalculatesCorrectly {
    all d: Dancer | {
        let mustHaveSatisfied = #(d.assignments & d.mustHavePreferences) |
        let preferencesSatisfied = #(d.assignments & d.preferences) |
        let avoidViolated = #(d.assignments & d.avoidPreferences) |
        
        dancerSatisfactionScore[d] = (multiply[mustHaveSatisfied, 3]) + preferencesSatisfied - (multiply[avoidViolated, 2])
    }
}

// test for scheduling conflict resolution
pred schedulingConflictResolution {
    some disj d1, d2: Dancer | some disj p1, p2, p3: Piece | {
        // two pieces have overlapping rehearsal slots
        some (p1.rehearsalSlots & p2.rehearsalSlots)
        
        // dancer 1 wants both conflicting pieces
        p1 in d1.mustHavePreferences
        p2 in d1.mustHavePreferences
        
        // but can only be assigned to one due to conflicts
        eventually (p1 in d1.assignments and p2 not in d1.assignments) or
                  (p1 not in d1.assignments and p2 in d1.assignments)
    }
}

// test for preference satisfaction vs. fairness
pred preferenceVsFairness {
    some disj d1, d2: Dancer | {
        // dancer 1 has a lot of strong preferences
        #d1.mustHavePreferences >= 3
        
        // dancer 2 has fewer preferences
        #d2.mustHavePreferences < #d1.mustHavePreferences
        
        // in fair distribution, dancer 1 can't get all their must-haves
        eventually {
            validAssignment
            #(d1.assignments & d1.mustHavePreferences) < #d1.mustHavePreferences
            abs[(assignmentCount[d1] - assignmentCount[d2])] <= 2
        }
    }
}

// test for competing preferences
// two dancers want the same piece, but it can only be assigned to one
pred competingPreferences {
    some disj d1, d2: Dancer | some p: Piece | {
        // both dancers really want the same piece
        p in d1.mustHavePreferences and p in d2.mustHavePreferences
        
        // the piece has limited capacity
        p.maxDancers = 1
        
        // only one dancer can get their preference satisfied
        eventually (p in d1.assignments and p not in d2.assignments) or
                  (p not in d1.assignments and p in d2.assignments)
    }
}

// test for balanced satisfaction across dancers
pred balancedSatisfaction {
    eventually {
        validAssignment
        all disj d1, d2: Dancer | {
            // satisfaction scores shouldn't differ by more than 3 points
            abs[dancerSatisfactionScore[d1] - dancerSatisfactionScore[d2]] <= 3
        }
    }
}

// exploring preference vs. assignment possibilities!
test suite for eventuallyValidTrace {
    test expect {aDancerWithNoAvailabity: {dancerIsNeverAvailable and eventuallyValidTrace} is sat}
    test expect {popPieceUnassigned: {popularPieceGoesUnassigned and eventuallyValidTrace} is sat}
    test expect {preferenceAvailibility: {preferencesMatchAvailability and eventuallyValidTrace} is sat}
    test expect {evenDistribution: {evenPreferenceDistribution and eventuallyValidTrace} is sat}
    test expect {satisfactionScore: {satisfactionScoreCalculatesCorrectly and eventuallyValidTrace} is sat}

    // fails! in real life, it's possible to be in these situations but the model doesn't allow it (interestingly)
    // test expect {unfortunateSituation1: {assignedToAvoidedPieceDueToNecessity and eventuallyValidTrace} is sat}
    // test expect {unfortunateSituation2: {mustHaveNeverSatisfied and eventuallyValidTrace} is sat}

    test expect {everyoneAvoids: {allAvoidEverything and eventuallyValidTrace} is unsat}

    // it's interesting that there's just no trace that sees a dancer just not get what they want?
    test expect {dancerWantsToBeInEverything: {oneDancerWantsEveryPiece and eventuallyValidTrace} is unsat}

    // these "unfortunate situations" are interesting - they're unsat, meaning the model
    // doesn't allow dancers to be assigned to avoided pieces or for must-haves to go unsatisfied
    test expect {avoidedAssignment: {assignedToAvoidedPieceDueToNecessity and eventuallyValidTrace} is unsat}
    test expect {mustHaveUnsatisfied: {mustHaveNeverSatisfied and eventuallyValidTrace} is unsat}

    // conflict resolution tests
    test expect {resolveScheduleConflicts: {schedulingConflictResolution and eventuallyValidTrace} is sat}
    test expect {balanceDancerSatisfaction: {balancedSatisfaction and eventuallyValidTrace} is sat}
    test expect {preferencesVsFairnessTradeoff: {preferenceVsFairness and eventuallyValidTrace} is sat}
    test expect {fairAssignment: {FairDistribution and eventuallyValidTrace} is sat}
    test expect {dancersBothWant: {competingPreferences and eventuallyValidTrace} is sat}    

}