% Select a subset of constraints from the choices in order to eliminate every trace

% Input predicates:
%   choice/2(trace_id, declare_constraint): associate possible choices to each trace
%   action/1(action): actions participating in constraints
%
% Output predicate
%   selected/1(declare_constraint): the set of selected constraints

% trace/1 holds all the trace ids
trace(T) :- choice(T, _).

% constraint/1 holds all the constraints
constraint(C) :- choice(_, C).

% select a subset of the choices
{ selected(C) : choice(_, C) }.

holds(C) :- selected(C).

% each trace must violate at least one of the constraints
violated(T) :- choice(T, C), holds(C).
:- trace(T), not violated(T).

#show selected/1.
#show holds/1.
