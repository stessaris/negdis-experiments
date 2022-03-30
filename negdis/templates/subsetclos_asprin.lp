%%%%%%%%%%%%%%
%%%%%%% asprin optimisation statements

% Subset minimal wrt the closure constraints, and selected constraints for ties

#preference(p1,subset){ ${predicate_holds}(C) : ${predicate_constraint}(C) }.
#preference(p2,less(cardinality)){ ${predicate_selected}(C) : ${predicate_choice}(_, C) }.

#preference(p10,lexico){ 1::**p2; 2::**p1 }.
#optimize(p10).
