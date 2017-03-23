Require Import Utf8.

Inductive kind : Set :=
| k_type    : kind
| k_effect  : kind
| k_eff_row : kind
| k_arrow   : kind → kind → kind
.