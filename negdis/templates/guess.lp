% Select a subset of constraints from the choices in order to eliminate every trace

% Input predicates:
%   ${predicate_choice}(trace_id, declare_constraint): associate possible choices to each trace
%   ${predicate_action}(action): actions participating in constraints
%
% Output predicate
%   ${predicate_selected}(declare_constraint): the set of selected constraints
%   ${predicate_holds}(declare_constraint): the set of selected constraints derived from the selected

% select a subset of the choices
{ ${predicate_selected}(C) : ${predicate_choice}(_, C) }.

% each trace must be rejected by at least one of the holding constraints
rejected(T) :- ${predicate_choice}(T, C), ${predicate_holds}(C).
:- ${predicate_choice}(T, _), not rejected(T).
