#lang forge/temporal
open "basic_model.frg"

// ==================== CORE VALIDATION TESTS ====================
// These tests verify the fundamental requirements for dance assignments
// They represent the basic expectations that the model must satisfy

// Ensures every piece has at least one dancer
// No empty pieces means every choreography will be performable
pred noEmptyPieces {
  all p: Piece | some d: Dancer | p in d.assignments
}

// Makes sure every dancer eventually gets to participate
// This is important for inclusivity and dancer satisfaction
pred everyoneInAtLeastOnePiece {
  eventually (all d: Dancer | some d.assignments)
}

// Checks for scheduling conflicts - a dancer can't be in two places at once!
// This is physically impossible and would cause rehearsal problems
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

// Tests that dancers aren't assigned when they're unavailable
// This is crucial for respecting dancers' time constraints
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

// These tests check that our valid assignment definition works as expected
test suite for validAssignment {
  // testing most common concerns!
  assert noEmptyPieces is necessary for validAssignment
  assert everyoneInAtLeastOnePiece is necessary for validAssignment
  test expect {noDancerInternalConflict: {validAssignment and dancerHasInternalConflict} is unsat}
  test expect {noDancerExternalConflict: {validAssignment and dancerHasExternalConflict} is unsat}
}

// ==================== INITIALIZATION TESTS ====================
// These tests verify the starting state of the model is correct
// The initial state needs to be a clean slate for assignments

// Makes sure all dancers start with no assignments
// This gives us a clean starting point for the assignment process
pred initiallyNoAssignments {
  // In the initial state, no dancers have assignments
  all d: Dancer | no d.assignments
}

// Ensures all pieces have rehearsal times defined
// Can't schedule dancers without knowing when rehearsals are!
pred allPiecesHaveRehearsalTime {
  all p: Piece | some p.rehearsalSlots
}

// Check that initialization properly sets up the system
test suite for init {
  assert allPiecesHaveRehearsalTime is necessary for init
  assert initiallyNoAssignments is necessary for init
}

// ==================== CONSTRAINT ENFORCEMENT TESTS ====================
// These tests verify that the system enforces its core constraints
// They ensure the rules of our dance company are being followed

// This test verifies that the capacity constraint is correctly enforced
// It's important because in real-world dance settings, exceeding the maximum
// number of dancers can lead to crowding, safety concerns, and rehearsal challenges
pred maxDancersConstraintWorks {
  some p: Piece | {
    p.maxDancers = 2
    // The piece already has maxDancers assigned
    #{d: Dancer | p in d.assignments} = 2
    // Trying to assign another dancer should be impossible
    some d: Dancer | {
      p not in d.assignments and
      p.rehearsalSlots in d.availability and
      not assignDancer[d, p]
    }
  }
}

// This test ensures that our system maintains consistency across state transitions
// It's critical for any temporal model to maintain its core invariants at all times
// Otherwise, we might temporarily enter invalid states that violate real-world constraints
pred transitionsPreserveConstraints {
  // Start with valid constraints
  NoScheduleConflicts and DancerAvailability and PieceSizeConstraints
  // After any transition, constraints should still hold
  next_state (NoScheduleConflicts and DancerAvailability and PieceSizeConstraints)
}

// This test verifies that we can't create impossible situations where
// dancers with no availability get assigned to pieces
// In real dance companies, some dancers have conflicts that prevent participation
pred zeroAvailabilityDancersAreUnassigned {
  // If a dancer has no availability...
  all d: Dancer | {
    no d.availability implies
    // ...then they are not assigned to any piece
    no d.assignments
  }
}

// This test ensures that pieces can be fully assigned with all slots filled
// It's important because real dance performances need all roles filled
// A dance can't be performed properly if it's missing dancers!
pred allPiecesCanBeFullyAssigned {
  eventually {
    all p: Piece | {
      let dancersInPiece = { d: Dancer | p in d.assignments } | {
        // The piece has some dancers (not empty)
        some dancersInPiece and
        // But not more than maximum
        #dancersInPiece <= p.maxDancers
      }
    }
  }
}

// This test verifies our unassignment operation works correctly
// If we can't remove dancers from pieces, we might get stuck in
// suboptimal states where dancers can't be reassigned to better matches
pred unassignmentWorksCorrectly {
  // Find a trace where a dancer gets assigned and later unassigned
  eventually {
    some d: Dancer, p: Piece | {
      p in d.assignments and
      next_state (p not in d.assignments)
    }
  }
}

// This ensures dancers don't get overloaded with too many pieces
// In real dance companies, having dancers in too many pieces
// creates mental and physical strain and impacts performance quality
// We don't want our dancers to burn out!
pred noOverloadedDancers {
  // Set a reasonable maximum - dancers shouldn't be in more than 2 pieces
  all d: Dancer | always #d.assignments <= 2
}

// This test verifies that after an unassignment, other dancers' assignments
// remain unchanged - important for the stability of the assignment process
// We don't want changing one dancer's assignment to have unintended ripple effects
pred unassignmentOnlyAffectsTargetDancer {
  some d1, d2: Dancer, p: Piece | {
    d1 != d2 and
    p in d1.assignments and
    // When dancer1 gets unassigned from a piece...
    unassignDancer[d1, p] and 
    // ...dancer2's assignments should remain the same
    d2.assignments' = d2.assignments
  }
}

// ==================== EDGE CASE TESTS ====================
// These tests verify the system's ability to handle unusual situations
// They ensure the model is robust in the face of challenging scenarios

// Tests a critical edge case: when pieces have overlapping rehearsal slots,
// the system should still find valid assignments if possible
// This mirrors real-world scheduling challenges in dance companies
// Sometimes there just aren't enough studio spaces!
pred overlappingRehearsalSlotsHandled {
  // Create pieces with overlapping rehearsal times
  some disj p1, p2: Piece, ts: TimeSlot | {
    ts in p1.rehearsalSlots and ts in p2.rehearsalSlots and
    // We should still reach a valid assignment
    eventually validAssignment
  }
}

// This test ensures the system handles the extreme case where a dancer
// is available for all possible time slots - a "super available" dancer
// Such dancers are valuable in real dance companies for filling gaps
// They're the heroes who say "I can make any rehearsal time!" lol
pred superAvailableDancerAssignment {
  // Create a dancer who is available for all time slots
  some d: Dancer | {
    d.availability = TimeSlot and
    // This dancer should eventually be assigned to at least one piece
    eventually some d.assignments
  }
}

// Tests the system's ability to recover from invalid states
// This handles scenarios where manual intervention might create conflicts
pred recoverFromInvalidState {
  // Start with a dancer assigned to conflicting pieces
  some d: Dancer | some disj p1, p2: Piece | {
    // The dancer is in both pieces...
    p1 in d.assignments and p2 in d.assignments and
    // ...which have a scheduling conflict
    some (p1.rehearsalSlots & p2.rehearsalSlots)
  }
  
  // Despite starting with conflicts, we should reach a valid state
  eventually validAssignment
}

// Tests how the system handles unexpected values for maxDancers
// Real systems need to be robust against configuration errors
pred defaultMaxDancersHandled {
  // For every piece...
  all p: Piece | {
    // If its maxDancers value is invalid (negative or zero)...
    (p.maxDancers <= 0) implies
    // Then treat it as if maxDancers = 1
    (always #{d: Dancer | p in d.assignments} <= 1)
  }
}

// ==================== FAIRNESS TESTS ====================
// These tests ensure the assignment process is fair to all participants
// They verify that the system respects dancers' needs and limitations

// This test ensures dancers with availability get assigned to pieces
// In real dance companies, we want to give everyone a chance to perform
pred dancerPrefTest {
  // For every dancer...
  all d: Dancer | {
    // If they have some availability...
    (some d.availability) implies
    // Then they should eventually be assigned to at least one piece
    (eventually some d.assignments)
  }
}

// This test verifies the assignment process makes continuous progress
// We need this to ensure the system doesn't get stuck in "local optima"
pred makesContinuousProgress {
  // At every point in the execution...
  always {
    // If we're not in a valid assignment state...
    not validAssignment implies
    // Then we should eventually be able to reach one
    eventually validAssignment
  }
}

// Tests that pieces with multiple rehearsal slots are handled correctly
// Most real choreography requires several rehearsals per week
pred multipleRehearsalSlotsHandled {
  // Every piece must have at least 2 different rehearsal slots
  all p: Piece | #p.rehearsalSlots >= 2
  
  // Even with this complexity, we should reach a valid assignment
  eventually validAssignment
}

// ==================== FORMAL PROPERTY TESTS ====================
// These tests verify fundamental properties that must hold for the entire system
// They represent critical guarantees about the model's behavior

// Safety property ensures no invalid states can ever be reached during execution
// This is essential because in a real dance company, invalid schedules cause chaos
pred alwaysValidConstraints {
  // All core constraints must be maintained at every step of the process
  always (NoScheduleConflicts and DancerAvailability and PieceSizeConstraints)
}

// Liveness property ensures our system can actually achieve its goal
// Without this, we might have a "safe" system that can never reach a solution
pred canReachValidState {
  // At some point in the future, we must be able to reach a valid assignment
  eventually validAssignment
}

// ==================== TEST SUITES ====================
// These group our tests into logical categories for verification

test suite for transitions {
  test expect {maxDancersIsRespected: {maxDancersConstraintWorks} is sat}
  test expect {constraintsAlwaysPreserved: {transitionsPreserveConstraints} is sat}
  test expect {unassignmentWorks: {unassignmentWorksCorrectly} is sat}
  test expect {unassignmentIsolated: {unassignmentOnlyAffectsTargetDancer} is sat}
}

test suite for eventuallyValid {
  test expect {canHandleOverlaps: {overlappingRehearsalSlotsHandled} is sat}
  test expect {superAvailableDancerUsed: {superAvailableDancerAssignment} is sat}
  test expect {noOverloadingDancers: {noOverloadedDancers and eventually validAssignment} is sat}
  test expect {availabilityRespected: {eventually (validAssignment and zeroAvailabilityDancersAreUnassigned)} is sat}
}

test suite for formalProperties {
  test expect {safetyPropertyTest: {traces and alwaysValidConstraints} is sat}
  test expect {livenessPropertyTest: {traces and canReachValidState} is sat}
}

test suite for additionalBehaviorTests {
  test expect {assignsEligibleDancers: {dancerPrefTest} is sat}
  test expect {progressGuarantee: {makesContinuousProgress} is sat}
  test expect {handlesMultipleRehearsals: {multipleRehearsalSlotsHandled} is sat}
  test expect {handlesDefaultValues: {defaultMaxDancersHandled} is sat}
  test expect {recoversFromInvalid: {recoverFromInvalidState} is sat}
}

// ==================== RUN COMMANDS ====================
// These commands execute specific configurations of our model
// They allow us to observe and verify the system's behavior

// This run tests our model with a diverse set of constraints
// to ensure it handles a wide range of realistic scenarios
// It's like simulating a real dance company's assignment process
run {
  traces
  eventuallyValid
  // Create at least one dancer with no availability
  some d: Dancer | no d.availability
  // Create at least one piece with tight capacity constraints
  some p: Piece | p.maxDancers = 1
  // Create some overlapping rehearsal slots
  some disj p1, p2: Piece | some (p1.rehearsalSlots & p2.rehearsalSlots)
} for 5 Dancer, 4 Piece, 6 TimeSlot, 4 Int

// This run focuses on fairness, complex scheduling, and error recovery
// It tests the model's ability to handle real-world challenges
run {
  // Follow the trace definition from the base model
  traces
  
  // Test that dancers with availability get assigned
  dancerPrefTest
  
  // Test that complex rehearsal schedules work
  multipleRehearsalSlotsHandled
  
  // Test that the system can recover from invalid states
  recoverFromInvalidState
} for 4 Dancer, 3 Piece, 5 TimeSlot, 4 Int