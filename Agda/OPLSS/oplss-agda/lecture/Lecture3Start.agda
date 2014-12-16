open import Preliminaries

module lecture.Lecture3Start where

  open Vector using (Vec ; [] ; _::_)
  open Nat using (_+_)
  open List using (_++_ ; [_] ; ++-assoc)

  String = List Char

  lit : Char → String
  lit c = c :: []

  