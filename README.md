# README

This project uses Temporal Forge to model and analyze the problem of assigning dancers to dance pieces over time, subject to constraints like availability, scheduling conflicts, and dancer preferences. The model explores how fair and feasible rehearsal assignments can be made dynamically in a way that respects both logistical constraints and individual dancer needs.

##  Overview

The model aims to simulate how dancers are assigned to pieces across time in a fair and realistic way. It represents the piece selection process as a sequence of state transitions governed by constraints. These constraints reflect the logistical issues dance organizations have to sort out while planning their pieces for a phase: limited availability, (possibly overlapping) rehearsal times, and piece capacity. In the more advanced version of the model, we also incorporate dancer preferences (the pieces they hope to join most, are okay with, or want to avoid) which adds another layer of complexity.

## Model Structure

The core of the model consists of three key signatures: *Dancer*, *Piece*, and *TimeSlot*. Each dancer has a set of available time slots and can be assigned to multiple pieces over time, while each piece has a set of required rehearsal slots and a maximum number of dancers. In the extended version of the model, dancers also have three tiers of preferences for pieces: mustHave, prefer, and avoid.

The model begins with an *init* predicate that sets up an empty assignment state where no dancers have been assigned to any pieces, each piece has rehearsals, and each dancer has at least some availability. Transitions are defined through predicates like *assignDancer* and *unassignDancer*, which allow dancers to be added to or removed from pieces if doing so would not violate availability or scheduling constraints. 

The model uses a *traces* predicate to organize valid execution paths over time. These paths start from the initial state and evolve through valid transitions until a satisfactory end state is reached. The *eventuallyValid* predicate ensures that some future state must satisfy the full set of assignment constraints, including capacity, availability, and (in the relevant version) preference enforcement, defined in *validAssignment*.

## Design Choices and Tradeoffs

One of our main design decisions was how to represent dancer preferences. We initially attempted a ranked list or numeric scoring system, but found it too complex to encode and reason about in Forge. We switched to a tiered system (*mustHave*, *prefer*, *avoid*), which offered a clearer and more flexible way to express soft preferences without relying on fragile numeric logic (which we saw could get out of hand with more than 7 pieces because of bitwidth restrictions). This choice made the model more expressive while keeping constraints manageable.

**
We also chose to model assignment changes temporally, allowing dancers to be incrementally added or removed across time steps. This better reflects the real scheduling dynamics an e-board navigates, like iteratively refining casts, rather than assuming a single instant where everything is assigned. To keep the model manageable, we simplified piece scheduling by fixing rehearsal slots per piece, avoiding the complexity of choosing rehearsal times dynamically. Finally, we scoped our fairness modeling to the dancer’s perspective (excluding choreographer input, for example) in order to focus more clearly on logistical feasibility and equitable distribution of opportunity.
**


## Scope and Assumptions

All rehearsal slots are treated as atomic and of equal duration, and each piece must have at least one rehearsal slot. Dancer availability is binary (available or not for a given slot), and preferences are modeled as static sets rather than changing over time. Piece constraints are also static and specific, whereas in real life, a choreographer could mark that they'd accept any number of dancers for their piece.

It also assumes perfect knowledge of all dancer availability and preferences from the start, which may not reflect real-world situations where this information unfolds gradually (someone getting sick, for example). These simplifications were necessary to keep the model possible in Forge, but they also highlight areas for potential future development.

## Changes from the Proposal

** (I'm thinking here we can talk about the visualizer!!) **

## What the Model Proves

The model demonstrates that a valid assignment state is achievable under basic logistical constraints. In this state, no dancer is double-booked, all rehearsal availability is respected, and no piece exceeds its maximum capacity. However, once strong or conflicting preferences are introduced, the model reveals that it is often impossible to satisfy everyone's must-haves and avoids while still maintaining a conflict-free and valid assignment.

What the model can achieve instead is a fairer distribution of satisfaction across dancers. Rather than maximizing preference fulfillment for a few individuals, the model supports solutions that aim for a more equal standard of satisfaction across the team. These findings highlight the tension between individual preferences and collective feasibility.

(there's a couple of tests i can reference here, the commented out pair of unfortunate situations lol / do we want to do the compare to existing prefs here)

## Understanding Model Instances and Visualization

Upon running a trace, each instance has a sequence of states that show how assignments evolve over time. To interpret a sample instance, begin by looking at the initial state to see which dancer availability and piece rehearsal slot designation, and then step forward through the trace to see assignments. 

(next part dependent on visualizer status!!)

**
We found it helpful to mark all the attributes of the Sigs (rehearsalSlots, availability, min/maxDancers, etc) as attributes, and just leave the assignments to be visualized with arrows.
**

## Collaboration