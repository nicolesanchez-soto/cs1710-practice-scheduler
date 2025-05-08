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

We also chose to model assignment changes temporally, allowing dancers to be added or removed across time steps. This better reflects the real scheduling dynamics an e-board navigates, like iteratively refining casts, rather than assuming a single instant where everything is assigned. To keep the model manageable, we simplified piece scheduling by fixing rehearsal slots per piece, avoiding the complexity of choosing rehearsal times dynamically. Finally, we scoped our fairness modeling to the dancer’s perspective (excluding choreographer input, for example) in order to focus more clearly on logistical feasibility and equitable distribution of opportunity.


## Scope and Assumptions

All rehearsal slots are treated as atomic and of equal duration, and each piece must have at least one rehearsal slot. Dancer availability is binary (available or not for a given slot), and preferences are modeled as static sets rather than changing over time. Piece constraints are also static and specific, whereas in real life, a choreographer could mark that they'd accept any number of dancers for their piece.

It also assumes perfect knowledge of all dancer availability and preferences from the start, which may not reflect real-world situations where this information unfolds gradually (someone getting sick, for example). These simplifications were necessary to keep the model possible in Forge, but they also highlight areas for potential future development.

## Changes from the Proposal

One of the biggest changes from our original proposal was our plan for visualization. We initially wanted to create a custom visualizer that would look like an actual dance team schedule - basically a colorful table or spreadsheet (which is what most E-boards use when manually making assignments), with dancers' names, pieces, and time slots all organized neatly.

We checked "Yes" on the intention to create a custom visualizer script, but honestly, we hit some walls with this. When we tried implementing it with JavaScript to work with Sterling, we ran into several issues:

First, showing all the temporal data (like who's assigned when and where) in a table format while still keeping all the constraint relationships visible was way harder than we thought. The connections between time slots, pieces, and dancers got a bit messy to display correctly.

Second, we underestimated how much work it would take to modify Sterling to show something completely different from its origional visualization. We spent a few late nights trying different approaches but kept hitting dead ends with the integration.

We also probably bit off more than we could chew given our coding experience with Sterling's visualization system. None of us had worked with it before, and the learning curve was steeper than expected.

Instead, we pivoted to work more on the model itself and found that with careful sig organization, some color-coding and filtering using Cope and Drag in the default Sterling visualization, we could still make the output readable enough for our purposes. We marked all the attributes of the Sigs (rehearsalSlots, availability, min/maxDancers, etc.) as attributes in the visualizer and left the assignments to be visualized with arrows, which actually worked pretty well.

This change let us focus more on what we cared about most - getting the preference weighting system and conflict resolution to work correctly.

## What the Model Proves

The model demonstrates that a valid assignment state is achievable under basic logistical constraints. In this state, no dancer is double-booked, all rehearsal availability is respected, and no piece exceeds its maximum capacity. However, once strong or conflicting preferences are introduced, the model reveals that it is often impossible to satisfy everyone's must-haves and avoids while still maintaining a conflict-free and valid assignment.

What the model can achieve instead is a fairer distribution of satisfaction across dancers. Rather than maximizing preference fulfillment for a few individuals, the model supports solutions that aim for a more equal standard of satisfaction across the team. These findings highlight the tension between individual preferences and collective feasibility.

## Understanding Model Instances and Visualization

Upon running a trace, each instance represents a timeline of system states showing how dancers are gradually assigned to pieces. These states form a progression: you can start with the **initial state** to understand the foundational setup—who is available when, which rehearsal slots are linked to each piece, and what the initial preferences are. From there, you can step forward through the trace to see how dancer-piece assignments evolve.

We found it helpful to **treat all static attributes of the signatures—like `availability`, `rehearsalSlots`, `minDancers`, and `maxDancers`—as attributes in the visualizer**, and to **leave the dynamic dancer-to-piece assignments as arrows**. This keeps the visualization readable and focused, making it easier to spot trends in how dancers get assigned over time.

The most interesting patterns usually emerge around the middle, where you can see the model making tradeoffs between availability constraints and preference satisfaction. For complex conflicts (like when two dancers want the same piece but have different availability), you'll notice the model favoring feasible, fair outcomes—sometimes satisfying strong preferences, and other times distributing assignments more evenly to maintain fairness and avoid scheduling conflicts.

## Collaboration

N/A