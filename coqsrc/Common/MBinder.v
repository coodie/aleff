Require Import Utf8.

Inductive inc (V : Set) : Set :=
| VZ : inc V
| VS : V → inc V
.

Arguments VZ [V].
Arguments VS [V] _.

Inductive inc2_h (V : Set) : Set :=
| V2_arg    : inc2_h V
| V2_resume : inc2_h V
| V2S       : V → inc2_h V
.

Arguments V2_arg    [V].
Arguments V2_resume [V].
Arguments V2S       [V] _.