Require Import Utf8.
Require Common.Var.

Module Var  := Common.Var.Make.
Module TVar := Common.Var.Make.

Definition var  := Var.t.
Definition tvar := Var.t.