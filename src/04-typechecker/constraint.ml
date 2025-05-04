module Ast = Language.Ast

type 'a t =
  | TypeConstraint of ('a Ast.ty * 'a Ast.ty)
  | TauConstraint of ('a Ast.tau * 'a Ast.tau)
  | TauGeq of ('a Ast.tau * 'a Ast.tau)

let type_constraint v = TypeConstraint v
let tau_constraint v = TauConstraint v
let tau_geq v = TauGeq v

let is_type_constraint = function
  | TypeConstraint _ -> true
  | TauConstraint _ -> false
  | TauGeq _ -> false

let is_tau_constraint = function
  | TypeConstraint _ -> false
  | TauConstraint _ -> true
  | TauGeq _ -> false

let is_tau_geq = function
  | TypeConstraint _ -> false
  | TauConstraint _ -> false
  | TauGeq _ -> true

let find_type_constraint = function
  | TypeConstraint v -> Some v
  | TauConstraint _ -> None
  | TauGeq _ -> None

let find_tau_constraint = function
  | TypeConstraint _ -> None
  | TauConstraint v -> Some v
  | TauGeq _ -> None

let find_tau_geq = function
  | TypeConstraint _ -> None
  | TauConstraint _ -> None
  | TauGeq v -> Some v

let map_type_constraint f = function
  | TypeConstraint v -> TypeConstraint (f v)
  | TauConstraint _ as e -> e
  | TauGeq _ as e -> e

let map_tau_constraint f = function
  | TypeConstraint _ as e -> e
  | TauConstraint v -> TauConstraint (f v)
  | TauGeq _ as e -> e

let map_tau_geq f = function
  | TypeConstraint _ as e -> e
  | TauConstraint _ as e -> e
  | TauGeq v -> TauGeq (f v)

let map ~type_constraint ~tau_constraint ~tau_geq = function
  | TypeConstraint v -> TypeConstraint (type_constraint v)
  | TauConstraint v -> TauConstraint (tau_constraint v)
  | TauGeq v -> TauGeq (tau_geq v)

let fold ~type_constraint ~tau_constraint ~tau_geq = function
  | TypeConstraint v -> type_constraint v
  | TauConstraint v -> tau_constraint v
  | TauGeq v -> tau_geq v

let iter = fold
let for_all = fold

let equal ~type_constraint ~tau_constraint ~tau_geq e1 e2 =
  match (e1, e2) with
  | TypeConstraint v1, TypeConstraint v2 -> type_constraint v1 v2
  | TauConstraint v1, TauConstraint v2 -> tau_constraint v1 v2
  | TauGeq v1, TauGeq v2 -> tau_geq v1 v2
  | TypeConstraint _, TauConstraint _
  | TypeConstraint _, TauGeq _
  | TauConstraint _, TypeConstraint _
  | TauConstraint _, TauGeq _
  | TauGeq _, TypeConstraint _
  | TauGeq _, TauConstraint _ ->
      false

let compare ~type_constraint ~tau_constraint ~tau_geq e1 e2 =
  match (e1, e2) with
  | TypeConstraint v1, TypeConstraint v2 -> type_constraint v1 v2
  | TauConstraint v1, TauConstraint v2 -> tau_constraint v1 v2
  | TauGeq v1, TauGeq v2 -> tau_geq v1 v2
  | TypeConstraint _, TauConstraint _ -> 1
  | TypeConstraint _, TauGeq _ -> 1
  | TauConstraint _, TypeConstraint _ -> -1
  | TauConstraint _, TauGeq _ -> 1
  | TauGeq _, TypeConstraint _ -> -1
  | TauGeq _, TauConstraint _ -> -1
