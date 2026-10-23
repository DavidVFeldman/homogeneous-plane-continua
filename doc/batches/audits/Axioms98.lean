import HPC.Plane.Organ98

-- Item 1: the organ is snake-like
#print axioms HPC.Plane.isSnakeLike_univ_of_epsMap
#print axioms HPC.Plane.isSnakeLike_of_epsMap
#print axioms HPC.Plane.Org.continuous_organZig
#print axioms HPC.Plane.Org.dist_le_of_organZig_eq
#print axioms HPC.Plane.organ_isSnakeLike
-- Item 2: condition A
#print axioms HPC.Plane.organ_condA_layer
#print axioms HPC.Plane.organ_condA_H
#print axioms HPC.Plane.organ_condA_K
#print axioms HPC.Plane.organ_condA_H_or_K
-- Item 3: terminal layer and gluing
#print axioms HPC.Plane.good_layer_terminal
#print axioms HPC.Plane.organ_layer_terminal
#print axioms HPC.Plane.organ_sides_glue
#print axioms HPC.Plane.two_organs_counterexample
#print axioms HPC.Plane.isSnakeLike_union_of_terminal_refuted
-- Item 3, degenerate case: two arcs through a point
#print axioms HPC.Plane.arcs_counterexample
