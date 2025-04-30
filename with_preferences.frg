#lang forge/temporal

option max_tracelength 10
option min_tracelength 5

/*-----------------------------------------------------------------
 * MODEL OVERVIEW
 *-----------------------------------------------------------------*/

/* Dancer Assignment Model - Enhanced Version with Preferences
 *
 * This model represents how dancers in a dance group get assigned to pieces, with preferences.
 *
 * Key enhancements to the foundation model:
 * 1. Preference system: Dancers have preferences for which pieces they want to join
 * 2. Preference strength: Multiple preference levels (must-have, preferred, neutral, avoid)
 * 3. Optimization metrics: The model tracks satisfaction of preferences over time
 * 4. Fairness considerations: The system tries to distribute opportunities fairly
 *
 * The model still maintains the original constraints:
 * - No double-booking (schedule conflicts)
 * - Piece size limits
 * - Dancer availability requirements
 *
 * But now it also tries to optimize for dancer satisfaction based on preferences.
 */

/*-----------------------------------------------------------------
 * SIGNATURE DEFINITIONS
 *-----------------------------------------------------------------*/

/* The Dancer signature represents each performer in the dance group.
 * Enhanced with preference relationships to pieces.
 */
sig Dancer {
    // When a dancer is free for rehearsals
    availability: set TimeSlot,
    
    // Which pieces a dancer is assigned to (changes over time)
    var assignments: set Piece,
    
    // NEW: Strong preferences - pieces the dancer really wants to join
    mustHavePreferences: set Piece,
    
    // NEW: Mild preferences - pieces the dancer would like to join
    preferences: set Piece,
    
    // NEW: Pieces the dancer would prefer to avoid
    avoidPreferences: set Piece
}

/* The Piece signature represents each dance performance/choreography.
 * Enhanced with preference tracking.
 */
sig Piece {
    // When the piece rehearses
    rehearsalSlots: set TimeSlot,
    
    // Maximum number of dancers allowed
    maxDancers: one Int,
    
    // NEW: Minimum number of dancers required
    minDancers: one Int
}

/* TimeSlot signature remains unchanged */
sig TimeSlot {}

/*-----------------------------------------------------------------
 * CORE CONSTRAINTS (from foundation model)
 *-----------------------------------------------------------------*/

/* Ensures dancers cannot be double-booked */
pred NoScheduleConflicts {
    all d: Dancer | {
        all disj p1, p2: Piece | {
            (p1 in d.assignments and p2 in d.assignments) implies {
                no (p1.rehearsalSlots & p2.rehearsalSlots)
            }
        }
    }
}

/* Ensures dancers are only assigned when available */
pred DancerAvailability {
    all d: Dancer, p: Piece | {
        p in d.assignments implies {
            p.rehearsalSlots in d.availability
        }
    }
}

/* Ensures pieces don't exceed max dancer capacity */
pred PieceSizeConstraints {
    all p: Piece | {
        let dancersInPiece = { d: Dancer | p in d.assignments } | {
            // Enforce both minimum and maximum
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
    (mul[mustHaveSatisfied, 3]) + preferencesSatisfied - (mul[avoidViolated, 2])
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
    
    // Try to avoid assigning dancers to pieces they want to avoid
    // Note: This is a soft constraint that may be violated if necessary
    all d: Dancer | {
        // Minimize overlap between assignments and avoid preferences
        #(d.assignments & d.avoidPreferences) <= 1
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
        (assignmentCount[d1] - assignmentCount[d2]).abs <= 2
    }
}

/*-----------------------------------------------------------------
 * PREDICATES FOR STATE VALIDATION
 *-----------------------------------------------------------------*/

/* Checks if the current state represents a valid assignment */
pred validAssignment {
    // Every piece must have dancers assigned
    all p: Piece | some d: Dancer | p in d.assignments
    
    // Core constraints must be satisfied
    NoScheduleConflicts
    DancerAvailability
    PieceSizeConstraints
    
    // NEW: Preference considerations
    // This makes it a goal to satisfy preferences when possible
    PreferenceConstraints
    
    // NEW: Fairness considerations
    FairDistribution
}

/* Defines the initial state with no assignments */
pred init {
    // No dancers are assigned to pieces initially
    all d: Dancer | no d.assignments

    // Set up different availability patterns
    some d: Dancer | some t: TimeSlot | t not in d.availability

    // Every piece has at least one rehearsal slot
    all p: Piece | some p.rehearsalSlots
    
    // Ensure preferences are properly set up
    all d: Dancer | {
        // Must-have and avoid preferences shouldn't overlap
        no (d.mustHavePreferences & d.avoidPreferences)
        
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

/* Assigns a dancer to a piece, now considering preferences */
pred assignDancer[d: Dancer, p: Piece] {
    // --- PRECONDITIONS ---
    
    // The dancer must be available
    p.rehearsalSlots in d.availability
    
    // The dancer must not have scheduling conflicts
    all p2: Piece | {
        p2 in d.assignments implies {
            no (p.rehearsalSlots & p2.rehearsalSlots)
        }
    }
    
    // The piece must not be at maximum capacity
    let dancersInPiece = { d2: Dancer | p in d2.assignments } | {
        #dancersInPiece < p.maxDancers
    }
    
    // NEW: Preference-based conditions
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
    
    // Add the piece to assignments
    d.assignments' = d.assignments + p
    
    // --- FRAME CONDITION ---
    
    // Other dancers remain unchanged
    all d2: Dancer | d2 != d implies {
        d2.assignments' = d2.assignments
    }
}

/* Unassigns a dancer from a piece */
pred unassignDancer[d: Dancer, p: Piece] {
    // --- PRECONDITION ---
    
    // The dancer must currently be assigned to the piece
    p in d.assignments
    
    // NEW: Don't unassign if it would violate minimum dancers requirement
    let currentDancerCount = #{ d2: Dancer | p in d2.assignments } | {
        currentDancerCount > p.minDancers
    }
    
    // --- ACTION ---
    
    // Remove the piece from assignments
    d.assignments' = d.assignments - p
    
    // --- FRAME CONDITION ---
    
    // Other dancers remain unchanged
    all d2: Dancer | d2 != d implies {
        d2.assignments' = d2.assignments
    }
}

/* State remains unchanged */
pred stutter {
    all d: Dancer | d.assignments' = d.assignments
}

/*-----------------------------------------------------------------
 * TRACE DEFINITION
 *-----------------------------------------------------------------*/

/* Defines possible behaviors over time */
pred traces {
    // Start with no assignments
    init
    
    // For all future states, one of the following must occur
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
pred eventuallyOptimalValid {
    // Eventually reach a valid assignment
    eventually {
        validAssignment
        
        // Optimization goal: maximize total satisfaction
        // No other valid assignment state should have a higher score
        all dancers: Dancer, assignments: Piece -> univ | {
            // If there's another valid configuration with different assignments
            (validAssignment and dancers.assignments != Dancer.assignments) implies {
                // Then our current total satisfaction must be greater or equal
                totalSatisfactionScore >= sum[d: Dancer |
                    // Calculate hypothetical satisfaction for comparison
                ]
                    let hypotheticalAssignments = { p: Piece | p in d.assignments } |
                    let mustHaveSatisfied = #(hypotheticalAssignments & d.mustHavePreferences) |
                    let preferencesSatisfied = #(hypotheticalAssignments & d.preferences) |
                    let avoidViolated = #(hypotheticalAssignments & d.avoidPreferences) |
                    (mustHaveSatisfied * 3) + preferencesSatisfied - (avoidViolated * 2)
            
            }
        }
    }
}

/*-----------------------------------------------------------------
 * RUN COMMANDS
 *-----------------------------------------------------------------*/

/* Find a trace that leads to a valid assignment respecting preferences */
run {
    traces
    eventually validAssignment
} for 4 Dancer, 3 Piece, 5 TimeSlot, 4 Int

/* Find a trace that leads to an optimal valid assignment maximizing satisfaction */
run {
    traces
    eventuallyOptimalValid
} for 4 Dancer, 3 Piece, 5 TimeSlot, 4 Int