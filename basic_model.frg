#lang forge/temporal

option max_tracelength 10
option min_tracelength 5

/*-----------------------------------------------------------------
 * MODEL OVERVIEW
 *-----------------------------------------------------------------*/

/* Dancer Assignment Model - Foundation Version
 *
 * This model represents how dancers in a dance group get assigned to pieces.
 *
 * In real life, this is a complex process with many constraints:
 * - Each dancer has limited availability (they can't make every rehearsal time)
 * - Pieces have specific rehearsal schedules
 * - A dancer can't be in two places at once (no schedule conflicts)
 * - Each piece has a maximum number of dancers it can accommodate
 *
 * This foundation model focuses on the basic mechanics:
 * 1. Representing dancers, rehearsals, and scheduling conflicts
 * 2. Modeling hard constraints like no double-booking and piece size limits
 * 3. Including basic availability inputs
 * 4. Ensuring the model produces valid placements that respect time constraints
 *
 * The model tracks how dancer assignments evolve over time, starting from
 * an initial state where no dancers are assigned, and progressing through
 * assignments and unassignments until reaching a valid configuration.
 */

/*-----------------------------------------------------------------
 * SIGNATURE DEFINITIONS
 *-----------------------------------------------------------------*/

/* The Dancer signature represents each performer in the dance group.
 * Each dancer has:
 * - a set of time slots when they're available for rehearsals
 * - a set of pieces they're assigned to (which can change over time)
 *
 */
sig Dancer {
    // This represents when a dancer is free for rehearsals
    // It's a set of TimeSlots when the dancer can attend practice
    availability: set TimeSlot,
    
    // This tracks which pieces a dancer is assigned to over time
    // The 'var' keyword means this can change from one time step to the next
    var assignments: set Piece,

    // NEW: Strong preferences - pieces the dancer really wants to join
    mustHavePreferences: set Piece,
    
    // NEW: Mild preferences - pieces the dancer would like to join
    preferences: set Piece,
    
    // NEW: Pieces the dancer would prefer to avoid
    avoidPreferences: set Piece
}

/* The Piece signature represents each dance performance/choreography.
 * Each piece has:
 * - a set of time slots when its rehearsals occur
 * - a maximum number of dancers it can accommodate
 *
 * Note that these don't change over time - the rehearsal schedule and 
 * maximum dancers are fixed properties of each piece.
 */
sig Piece {
    // The specific time slots when this piece has rehearsals
    // For example, a piece might rehearse on Mondays 7-9pm and Wednesdays 6-8pm
    rehearsalSlots: set TimeSlot,
    
    // The maximum number of dancers this piece can accommodate
    // This might be based on choreography requirements or space limitations
    maxDancers: one Int,

    // The minimum number of dancers this piece can accommodate
    minDancers: one Int
}

/* The TimeSlot signature represents specific time periods for rehearsals.
 * Each TimeSlot is a discrete unit of time when rehearsals can occur.
 * In real life, this might represent something like "Monday 7-9pm".
 *
 * This is an empty signature because we don't need additional properties
 * beyond the TimeSlot's existence.
 */
sig TimeSlot {}

/*-----------------------------------------------------------------
 * CORE CONSTRAINTS
 *-----------------------------------------------------------------*/

/* The NoScheduleConflicts predicate ensures dancers cannot be double-booked.
 * It checks that if a dancer is assigned to two different pieces, those
 * pieces must not rehearse at the same time.
 *
 * This is a critical constraint - in real life, a dancer physically cannot
 * be in two places at once. 
 */
pred NoScheduleConflicts {
    // Every piece has at least one rehearsal slot
    //***Moving this up here makes assertion 3 pass!
    all p: Piece | some p.rehearsalSlots

    // For every dancer...
    all d: Dancer | {
        // ...and for every distinct pair of pieces p1 and p2...
        all disj p1, p2: Piece | {
            // ...if the dancer is assigned to both pieces...
            (p1 in d.assignments and p2 in d.assignments) implies {
                // ...then there must be no overlap in rehearsal times
                // The & operator computes the intersection of two sets
                // 'no' checks that the intersection is empty
                no (p1.rehearsalSlots & p2.rehearsalSlots)
            }
        }
    }
}

/* The DancerAvailability predicate ensures dancers are only assigned to
 * pieces when they're available for all of that piece's rehearsals.
 *
 * This prevents assigning dancers to pieces they can't fully commit to
 * due to schedule limitations.
 */
pred DancerAvailability {
    // For every dancer and every piece...
    all d: Dancer, p: Piece | {
        // ...if the dancer is assigned to the piece...
        p in d.assignments implies {
            // ...then all rehearsal slots for that piece must be times
            // when the dancer is available
            // The 'in' operator checks that the left set is a subset of the right set
            p.rehearsalSlots in d.availability
        }
    }
}

/* The PieceSizeConstraints predicate ensures pieces don't exceed their
 * maximum dancer capacity.
 *
 * In real life, this constraint might exist because:
 * - Limited physical space for dancers
 * - Choreography requirements
 * - Practical management considerations
 */
pred PieceSizeConstraints {
    // For every piece...
    all p: Piece | {
        // ...define a set of all dancers assigned to this piece
        // This is a set comprehension expression that creates a set of
        // all dancers where the piece is in their assignments
        let dancersInPiece = { d: Dancer | p in d.assignments } | {
            // ...then ensure the number of dancers doesn't exceed the maximum
            // The # operator counts the number of elements in a set
            #dancersInPiece <= p.maxDancers and
            #dancersInPiece >= p.minDancers
        }
    }
}

/*-----------------------------------------------------------------
 * NEW PREFERENCE-RELATED PREDICATES
 *-----------------------------------------------------------------*/

/* Calculates a dancer's satisfaction score based on their assignments
 * and preferences. Higher score means better satisfaction.
 *
 * Scoring:
 * +3 points for each must-have preference satisfied
 * +1 point for each regular preference satisfied
 * -2 points for each avoided preference assigned
 */
fun dancerSatisfactionScore[d: Dancer]: Int {
    // Points for must-have preferences that were satisfied
    let mustHaveSatisfied = #(d.assignments & d.mustHavePreferences) |
    // Points for regular preferences that were satisfied
    let preferencesSatisfied = #(d.assignments & d.preferences) |
    // Negative points for avoided pieces that were assigned anyway
    let avoidViolated = #(d.assignments & d.avoidPreferences) |
    
    // Calculate total score using weighted values
    (multiply[mustHaveSatisfied, 3]) + preferencesSatisfied - (multiply[avoidViolated, 2])
}

/* Calculates the overall satisfaction score for all dancers.
 * This gives us a metric to optimize.
 */
fun totalSatisfactionScore: Int {
    sum d: Dancer | dancerSatisfactionScore[d]
}

/* The PreferenceConstraints predicate ensures some basic preference rules
 * are enforced. These are "soft constraints" that should be satisfied when possible.
 */
pred PreferenceConstraints {
    // Try to assign dancers to at least one of their must-have preferences
    // if they have any and if it's feasible
    all d: Dancer | some d.mustHavePreferences implies {
        some (d.assignments & d.mustHavePreferences)
    }

    // Pieces can only be in one of the 3 preferences at a time
    //*** Assertion pieceInOnePrefTierOnly fails without this adjustment
    // all p: Piece, d: Dancer | {
    //     // Count how many times this piece appears in each preference set
    //     let mustHaveCount = #(p & d.mustHavePreferences) |
    //     let preferencesCount = #(p & d.preferences) |
    //     let avoidCount = #(p & d.avoidPreferences) |
        
    //     // Ensure the piece is only in one of the three sets and there must be at least one piece in mustHave
    //     mustHaveCount + preferencesCount + avoidCount <= 1
    // }
    all d: Dancer | {
        no (d.mustHavePreferences & d.preferences & d.avoidPreferences)
    }
    
    // Try to avoid assigning dancers to pieces they want to avoid
    all d: Dancer | {
        // hard constraint version
        #(d.assignments & d.avoidPreferences) < 1
        // soft constraint version. Minimize overlap between assignments and avoid preferences
        //#(d.assignments & d.avoidPreferences) <= 1
    }
}

/*-----------------------------------------------------------------
 * FAIRNESS METRICS
 *-----------------------------------------------------------------*/

/* Calculates how many pieces a dancer is assigned to */
fun assignmentCount[d: Dancer]: Int {
    #d.assignments
}

/* Checks if assignments are relatively balanced across dancers */
pred FairDistribution {
    // The difference in assignment count between any two dancers
    // should not exceed 2 pieces
    all d1, d2: Dancer | {
        abs[(assignmentCount[d1] - assignmentCount[d2])] <= 2
    }
}

/*-----------------------------------------------------------------
 * PREDICATES FOR STATE VALIDATION
 *-----------------------------------------------------------------*/

/* The validAssignment predicate checks if the current state represents
 * a valid assignment of dancers to pieces.
 *
 * This is used to define our goal state - we want to eventually reach
 * a state where all pieces have dancers and all constraints are satisfied.
 */
pred validAssignment {
    // Every piece must have at least one dancer assigned to it
    // This prevents empty pieces with no dancers
    all p: Piece | some d: Dancer | p in d.assignments

    // Every dancer should be assigned to at least one piece
    all d: Dancer | some p: Piece | p in d.assignments
    
    // All core constraints must be satisfied
    NoScheduleConflicts
    DancerAvailability
    PieceSizeConstraints

    // Satisfy preference constraints when possible
    PreferenceConstraints

    // Fairness considerations
    FairDistribution
}

/* The init predicate defines the initial state of our system.
 * In this state, no dancers are assigned to any pieces yet.
 * This gives us a clean starting point for the assignment process.
 */
pred init {
    // Every dancer starts with an empty set of assignments
    // 'no' means the set must be empty
    all d: Dancer | no d.assignments

    // Set up different availability patterns for dancers, 
    // not all dancers are available for all time slots
    some d: Dancer | some t: TimeSlot | t not in d.availability

    // Every piece has at least one rehearsal slot
    //*** Upon testing, this does not seem to be enforced.....
    all p: Piece | some p.rehearsalSlots
    
    // Ensure preferences are properly set up
    all d: Dancer | {
        // Must-have and avoid preferences shouldn't overlap
        no (d.mustHavePreferences & d.avoidPreferences)

        // Preferences and avoid preferences should be disjoint
        no (d.preferences & d.avoidPreferences)

        // Must-have and preferences should be disjoint
        no (d.mustHavePreferences & d.preferences)
        
        // Preferences should be realistic - dancers must be available
        all p: Piece | p in d.mustHavePreferences or p in d.preferences implies {
            p.rehearsalSlots in d.availability
        }
        
        // Minimum dancers is at least 1 and less than maximum
        all p: Piece | p.minDancers >= 1 and p.minDancers <= p.maxDancers
    }
}

/*-----------------------------------------------------------------
 * STATE TRANSITION PREDICATES
 *-----------------------------------------------------------------*/

/* The assignDancer predicate defines how a dancer gets assigned to a piece.
 * It checks preconditions, specifies the change to make, and includes
 * frame conditions to keep other parts of the state unchanged.
 *
 * Parameters:
 * - d: the dancer being assigned
 * - p: the piece they're being assigned to
 */
pred assignDancer[d: Dancer, p: Piece] {
    // --- PRECONDITIONS ---
    
    // The dancer must be available for all rehearsal slots of the piece
    // This enforces the availability constraint before making the assignment
    p.rehearsalSlots in d.availability
    
    // The dancer must not have scheduling conflicts with their existing assignments
    // This checks that adding this piece won't create double-booking
    all p2: Piece | {
        p2 in d.assignments implies {
            no (p.rehearsalSlots & p2.rehearsalSlots)
        }
    }
    
    // The piece must not already be at maximum capacity
    // This ensures we don't exceed the piece's dancer limit
    let dancersInPiece = { d2: Dancer | p in d2.assignments } | {
        #dancersInPiece < p.maxDancers
    }
    
    // Prioritize must-have preferences or regular preferences
    // Only assign to avoided pieces if necessary
    p in d.mustHavePreferences or 
    p in d.preferences or
    (p in d.avoidPreferences implies {
        // Only assign to avoided pieces if:
        // 1. The piece needs more dancers to meet minimum requirements
        let currentDancerCount = #{ d2: Dancer | p in d2.assignments } | {
            currentDancerCount < p.minDancers
        }
    })

    // --- ACTION ---
    
    // Add the piece to the dancer's assignments in the next state
    // The prime (') indicates the value in the next state
    // The + operator adds an element to a set
    d.assignments' = d.assignments + p
    
    // --- FRAME CONDITION ---
    
    // All other dancers' assignments remain unchanged
    // This specifies what DOESN'T change, which is important in temporal modeling
    all d2: Dancer | d2 != d implies {
        d2.assignments' = d2.assignments
    }
}

/* The unassignDancer predicate defines how a dancer gets removed from a piece.
 * Similar to assignDancer, it specifies preconditions, the change to make,
 * and frame conditions.
 *
 * Parameters:
 * - d: the dancer being unassigned
 * - p: the piece they're being removed from
 */
pred unassignDancer[d: Dancer, p: Piece] {
    // --- PRECONDITION ---
    
    // The dancer must currently be assigned to the piece
    // Cannot unassign from a piece they're not in
    p in d.assignments

    // Don't unassign if it would violate minimum dancers requirement
    let currentDancerCount = #{ d2: Dancer | p in d2.assignments } | {
        currentDancerCount > p.minDancers
    }
    
    // --- ACTION ---
    
    // Remove the piece from the dancer's assignments in the next state
    // The - operator removes an element from a set
    d.assignments' = d.assignments - p
    
    // --- FRAME CONDITION ---
    
    // All other dancers' assignments remain unchanged
    all d2: Dancer | d2 != d implies {
        d2.assignments' = d2.assignments
    }
}

/* The stutter predicate defines a "do nothing" transition where
 * the state remains unchanged from one time step to the next.
 *
 * This is important in temporal modeling because:
 * 1. It allows the system to stay in a state for multiple time steps
 * 2. It helps create lasso traces (looping traces) required by the solver
 * 3. It enables modeling scenarios where not every time step needs a change
 */
pred stutter {
    // All dancers' assignments remain exactly the same in the next state
    all d: Dancer | d.assignments' = d.assignments
}

/*-----------------------------------------------------------------
 * TRACE DEFINITION
 *-----------------------------------------------------------------*/

/* The traces predicate defines the possible behaviors of our system over time.
 * It specifies:
 * 1. The initial state
 * 2. The allowed transitions between states
 *
 * The temporal solver will search for sequences of states that satisfy
 * these constraints, forming valid execution traces of the system.
 */
pred traces {
    // Start in the initial state with no assignments
    init
    
    // For all future states, one of the following must occur:
    // 1. Do nothing (stutter)
    // 2. Assign a dancer to a piece
    // 3. Unassign a dancer from a piece
    // The 'always' keyword means this applies to every time step
    always {
        stutter or 
        (some d: Dancer, p: Piece | assignDancer[d, p]) or
        (some d: Dancer, p: Piece | unassignDancer[d, p])
    }
}
/*-----------------------------------------------------------------
 * OPTIMIZATION GOALS
 *-----------------------------------------------------------------*/

/* Specifies that we want to reach a valid assignment state
 * that also maximizes overall dancer satisfaction
 */
// pred eventuallyOptimalValid {
//     // Eventually reach a valid assignment
//     eventually {
//         validAssignment
        
//         // Optimization goal: maximize total satisfaction
//         // No other valid assignment state should have a higher score
//         all dancers: Dancer, assignments: Piece -> univ | {
//             // If there's another valid configuration with different assignments
//             (validAssignment and dancers.assignments != Dancer.assignments) implies {
//                 // Then our current total satisfaction must be greater or equal
//                 totalSatisfactionScore >= sum[d: Dancer | ]
//                     // Calculate hypothetical satisfaction for comparison
                
//                     let hypotheticalAssignments = { p: Piece | p in d.assignments } |
//                     let mustHaveSatisfied = #(hypotheticalAssignments & d.mustHavePreferences) |
//                     let preferencesSatisfied = #(hypotheticalAssignments & d.preferences) |
//                     let avoidViolated = #(hypotheticalAssignments & d.avoidPreferences) |
//                     (mustHaveSatisfied * 3) + preferencesSatisfied - (avoidViolated * 2)
            
//             }
//         }
//     }
// }

/*-----------------------------------------------------------------
 * PROPERTIES TO CHECK
 *-----------------------------------------------------------------*/

/* The eventuallyValid predicate specifies that at some point in time,
 * we want to reach a valid assignment state.
 *
 * This is our goal - we want the model to show us how to assign dancers
 * to pieces in a way that satisfies all constraints.
 */
pred eventuallyValid {
    // At some point in the future, a valid assignment must be reached
    // The 'eventually' keyword is a temporal operator meaning 
    // "at some current or future state"
    eventually validAssignment
}

/*-----------------------------------------------------------------
 * RUN COMMAND
 *-----------------------------------------------------------------*/

/* This run command asks Forge to find an execution trace that:
 * 1. Follows the allowed transitions in 'traces'
 * 2. Eventually reaches a valid assignment
 *
 * The scope limits:
 * - 4 dancers
 * - 3 pieces
 * - 5 time slots
 * - Integer values up to 4 (for maxDancers)
 *
 * Forge will find a sequence of states showing how dancers get
 * assigned to pieces over time until all constraints are satisfied.
 */
run {
    traces
    eventuallyValid
} for 4 Dancer, 3 Piece, 5 TimeSlot, 4 Int

/* Find a trace that leads to an optimal valid assignment maximizing satisfaction */
// run {
//     traces
//     eventuallyOptimalValid
// } for 4 Dancer, 3 Piece, 5 TimeSlot, 4 Int