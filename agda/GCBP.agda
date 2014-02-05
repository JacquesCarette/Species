open import HoTT

module GCBP where

  postulate gcbp : {A B A' B' : Set} -> (Coprod A A' ≃ Coprod B B') -> (A' ≃ B') -> (A ≃ B)
  -- XXX TODO: implement me!
