Require Import Coq.Logic.Eqdep.

Ltac inj_pair2_all :=
  repeat (match goal with
          | H: existT _ _ _ = existT _ _ _ |- _ =>
              apply inj_pair2 in H
          end; subst).
