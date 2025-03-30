open Utils
module Ast = Language.Ast
module Const = Language.Const
module Primitives = Language.Primitives

let poly_type ty =
  let a = Ast.TyParam.fresh "poly" in
  ([ a ], [], ty (Ast.TyParam a))

let unary_integer_op_ty =
  ( [],
    [],
    Ast.TyArrow
      ( Ast.TyConst Const.IntegerTy,
        Ast.CompTy (Ast.TyConst Const.IntegerTy, Context.TauConst 0) ) )

let binary_integer_op_ty =
  ( [],
    [],
    Ast.TyArrow
      ( Ast.TyTuple [ Ast.TyConst Const.IntegerTy; Ast.TyConst Const.IntegerTy ],
        Ast.CompTy (Ast.TyConst Const.IntegerTy, Context.TauConst 0) ) )

let unary_float_op_ty =
  ( [],
    [],
    Ast.TyArrow
      ( Ast.TyConst Const.FloatTy,
        Ast.CompTy (Ast.TyConst Const.FloatTy, Context.TauConst 0) ) )

let binary_float_op_ty =
  ( [],
    [],
    Ast.TyArrow
      ( Ast.TyTuple [ Ast.TyConst Const.FloatTy; Ast.TyConst Const.FloatTy ],
        Ast.CompTy (Ast.TyConst Const.FloatTy, Context.TauConst 0) ) )

let comparison_ty =
  poly_type (fun a ->
      Ast.TyArrow
        ( Ast.TyTuple [ a; a ],
          Ast.CompTy (Ast.TyConst Const.BooleanTy, Context.TauConst 0) ))

let primitive_type_scheme = function
  | Primitives.CompareEq -> comparison_ty
  | Primitives.CompareLt -> comparison_ty
  | Primitives.CompareGt -> comparison_ty
  | Primitives.CompareLe -> comparison_ty
  | Primitives.CompareGe -> comparison_ty
  | Primitives.CompareNe -> comparison_ty
  | Primitives.IntegerAdd -> binary_integer_op_ty
  | Primitives.IntegerMul -> binary_integer_op_ty
  | Primitives.IntegerSub -> binary_integer_op_ty
  | Primitives.IntegerDiv -> binary_integer_op_ty
  | Primitives.IntegerMod -> binary_integer_op_ty
  | Primitives.IntegerNeg -> unary_integer_op_ty
  | Primitives.FloatAdd -> binary_float_op_ty
  | Primitives.FloatMul -> binary_float_op_ty
  | Primitives.FloatSub -> binary_float_op_ty
  | Primitives.FloatDiv -> binary_float_op_ty
  | Primitives.FloatPow -> binary_float_op_ty
  | Primitives.FloatNeg -> unary_float_op_ty
  | Primitives.ToString ->
      poly_type (fun a ->
          Ast.TyArrow
            (a, Ast.CompTy (Ast.TyConst Const.StringTy, Context.TauConst 0)))
