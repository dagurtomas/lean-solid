import topology.locally_constant.algebra

variables (A : Type*) [ring A]

structure loc_const_lin (X Y : Type*) [topological_space X] [add_comm_group X] [module A X]
  [add_comm_group Y] [module A Y] extends locally_constant X Y :=
(is_linear_map : is_linear_map A to_fun)
