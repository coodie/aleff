Require Import Utf8.

Inductive inc (V : Set) : Set :=
| VZ : inc V
| VS : V → inc V
.

Inductive inc2_h (V : Set) : Set :=
| V2_arg    : inc2_h V
| V2_resume : inc2_h V
| V2S       : V → inc2_h V
.