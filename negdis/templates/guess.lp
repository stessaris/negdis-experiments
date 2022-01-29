% Select a subset of constraints from the choices in order to eliminate every trace

% Input predicates:
%   ${predicate_choice}/2(trace_id, declare_constraint): associate possible choices to each trace
%   ${predicate_action}/1(action): actions participating in constraints
%
% Output predicate
%   ${predicate_selected}/1(declare_constraint): the set of selected constraints

% trace/1 holds all the trace ids
trace(T) :- ${predicate_choice}(T, _).

% ${predicate_constraint}/1 holds all the constraints
${predicate_constraint}(C) :- ${predicate_choice}(_, C).

% select a subset of the choices
{ ${predicate_selected}(C) : ${predicate_choice}(_, C) }.

${predicate_holds}(C) :- ${predicate_selected}(C).

% each trace must be rejected by at least one of the holding constraints
rejected(T) :- ${predicate_choice}(T, C), ${predicate_holds}(C).
:- trace(T), not rejected(T).

#show ${predicate_selected}/1.
#show ${predicate_holds}/1.
