module Imp.AST where

type Var = String

data AExp =
    ANum Int
  | AId  Var
  | APlus  AExp AExp
  | AMinus AExp AExp
  | AMult  AExp AExp
  deriving (Eq, Show)

data BExp =
    BTrue
  | BFalse
  | BEq  AExp AExp
  | BNeq AExp AExp
  | BLe  AExp AExp
  | BGt  AExp AExp
  | BNot BExp
  | BAnd BExp BExp
  deriving (Eq, Show)

data WeakCom =
    CSkip'
  | CAssign' Var AExp
  | CSeq' WeakCom WeakCom
  deriving (Eq, Show)

data ComIf =
    CSkip''
  | CAssign'' Var AExp
  | CSeq'' ComIf ComIf
  | CIf'' BExp ComIf ComIf
  deriving (Eq, Show)

data Com =
    CSkip
  | CAssign Var AExp
  | CSeq Com Com
  | CIf BExp Com Com
  | CWhile BExp Com
  deriving (Eq, Show)
