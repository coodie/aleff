Require Import Utf8.

Module Type S.

Parameter t : Set.

End S.

Module Make : S.

Definition t : Set := nat.

End Make.