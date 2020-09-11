{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Macro where

import qualified Prelude
import qualified Basics
import qualified BinNums
import qualified Classes
import qualified Datatypes
import qualified Definitions
import qualified Fin
import qualified List
import qualified Logic
import qualified Rdefinitions

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

coq_Dt :: Definitions.Coq_ty -> Definitions.Coq_ty
coq_Dt _UU03c4_ =
  case _UU03c4_ of {
   Definitions.Real -> Definitions.Prod Definitions.Real Definitions.Real;
   Definitions.Nat -> Definitions.Nat;
   Definitions.Array n t -> Definitions.Array n (coq_Dt t);
   Definitions.Arrow t1 t2 -> Definitions.Arrow (coq_Dt t1) (coq_Dt t2);
   Definitions.Prod t1 t2 -> Definitions.Prod (coq_Dt t1) (coq_Dt t2);
   Definitions.Sum t1 t2 -> Definitions.Sum (coq_Dt t1) (coq_Dt t2)}

coq_Dctx :: (Datatypes.Coq_list Definitions.Coq_ty) -> Definitions.Ctx
            Definitions.Coq_ty
coq_Dctx _UU0393_ =
  List.map coq_Dt _UU0393_

coq_Dv :: (Datatypes.Coq_list Definitions.Coq_ty) -> Definitions.Coq_ty ->
          (Definitions.Var Definitions.Coq_ty) -> Definitions.Var
          Definitions.Coq_ty
coq_Dv _ _ v =
  case v of {
   Definitions.Top _UU0393_ _UU03c4_ -> Definitions.Top
    (List.map coq_Dt _UU0393_) (coq_Dt _UU03c4_);
   Definitions.Pop _UU0393_ _UU03c4_ _UU03c3_ t -> Definitions.Pop
    (List.map coq_Dt _UU0393_) (coq_Dt _UU03c4_) (coq_Dt _UU03c3_)
    (coq_Dv _UU0393_ _UU03c4_ t)}

coq_Dtm_clause_10_clause_1 :: ((Definitions.Ctx Definitions.Coq_ty) ->
                              Definitions.Coq_ty -> Definitions.Coq_tm ->
                              Definitions.Coq_tm) -> (Definitions.Ctx
                              Definitions.Coq_ty) -> Definitions.Coq_tm ->
                              Definitions.Coq_tm -> Definitions.Coq_tm ->
                              Definitions.Coq_tm -> Definitions.Coq_tm
coq_Dtm_clause_10_clause_1 _ _ _ refine0 _ refine =
  Definitions.Coq_tuple Definitions.Real Definitions.Real
    (Definitions.Coq_add (Definitions.Coq_first Definitions.Real
    Definitions.Real refine) (Definitions.Coq_first Definitions.Real
    Definitions.Real refine0)) (Definitions.Coq_add (Definitions.Coq_second
    Definitions.Real Definitions.Real refine) (Definitions.Coq_second
    Definitions.Real Definitions.Real refine0))

coq_Dtm_clause_10 :: ((Definitions.Ctx Definitions.Coq_ty) ->
                     Definitions.Coq_ty -> Definitions.Coq_tm ->
                     Definitions.Coq_tm) -> (Definitions.Ctx
                     Definitions.Coq_ty) -> Definitions.Coq_tm ->
                     Definitions.Coq_tm -> Definitions.Coq_tm ->
                     Definitions.Coq_tm
coq_Dtm_clause_10 dtm _UU0393_ _ refine t6 =
  let {refine0 = dtm _UU0393_ Definitions.Real t6} in
  Definitions.Coq_tuple Definitions.Real Definitions.Real
  (Definitions.Coq_add (Definitions.Coq_first Definitions.Real
  Definitions.Real refine) (Definitions.Coq_first Definitions.Real
  Definitions.Real refine0)) (Definitions.Coq_add (Definitions.Coq_second
  Definitions.Real Definitions.Real refine) (Definitions.Coq_second
  Definitions.Real Definitions.Real refine0))

coq_Dtm_clause_11_clause_1 :: ((Definitions.Ctx Definitions.Coq_ty) ->
                              Definitions.Coq_ty -> Definitions.Coq_tm ->
                              Definitions.Coq_tm) -> (Definitions.Ctx
                              Definitions.Coq_ty) -> Definitions.Coq_tm ->
                              Definitions.Coq_tm -> Definitions.Coq_tm ->
                              Definitions.Coq_tm -> Definitions.Coq_tm
coq_Dtm_clause_11_clause_1 _ _ _ refine0 _ refine =
  Definitions.Coq_tuple Definitions.Real Definitions.Real
    (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
    Definitions.Real refine) (Definitions.Coq_first Definitions.Real
    Definitions.Real refine0)) (Definitions.Coq_add (Definitions.Coq_mul
    (Definitions.Coq_first Definitions.Real Definitions.Real refine)
    (Definitions.Coq_second Definitions.Real Definitions.Real refine0))
    (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
    Definitions.Real refine0) (Definitions.Coq_second Definitions.Real
    Definitions.Real refine)))

coq_Dtm_clause_11 :: ((Definitions.Ctx Definitions.Coq_ty) ->
                     Definitions.Coq_ty -> Definitions.Coq_tm ->
                     Definitions.Coq_tm) -> (Definitions.Ctx
                     Definitions.Coq_ty) -> Definitions.Coq_tm ->
                     Definitions.Coq_tm -> Definitions.Coq_tm ->
                     Definitions.Coq_tm
coq_Dtm_clause_11 dtm _UU0393_ _ refine t8 =
  let {refine0 = dtm _UU0393_ Definitions.Real t8} in
  Definitions.Coq_tuple Definitions.Real Definitions.Real
  (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
  Definitions.Real refine) (Definitions.Coq_first Definitions.Real
  Definitions.Real refine0)) (Definitions.Coq_add (Definitions.Coq_mul
  (Definitions.Coq_first Definitions.Real Definitions.Real refine)
  (Definitions.Coq_second Definitions.Real Definitions.Real refine0))
  (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
  Definitions.Real refine0) (Definitions.Coq_second Definitions.Real
  Definitions.Real refine)))

coq_Dtm :: (Definitions.Ctx Definitions.Coq_ty) -> Definitions.Coq_ty ->
           Definitions.Coq_tm -> Definitions.Coq_tm
coq_Dtm _UU0393_ _ t =
  case t of {
   Definitions.Coq_var _UU03c4_ v -> Definitions.Coq_var (coq_Dt _UU03c4_)
    (coq_Dv _UU0393_ _UU03c4_ v);
   Definitions.Coq_app _UU03c4_ _UU03c3_ t0 t1 -> Definitions.Coq_app
    (let {
      dt _UU03c4_0 =
        case _UU03c4_0 of {
         Definitions.Real -> Definitions.Prod Definitions.Real
          Definitions.Real;
         Definitions.Nat -> Definitions.Nat;
         Definitions.Array n t2 -> Definitions.Array n (dt t2);
         Definitions.Arrow t2 t3 -> Definitions.Arrow (dt t2) (dt t3);
         Definitions.Prod t2 t3 -> Definitions.Prod (dt t2) (dt t3);
         Definitions.Sum t2 t3 -> Definitions.Sum (dt t2) (dt t3)}}
     in dt _UU03c4_)
    (let {
      dt _UU03c4_0 =
        case _UU03c4_0 of {
         Definitions.Real -> Definitions.Prod Definitions.Real
          Definitions.Real;
         Definitions.Nat -> Definitions.Nat;
         Definitions.Array n t2 -> Definitions.Array n (dt t2);
         Definitions.Arrow t2 t3 -> Definitions.Arrow (dt t2) (dt t3);
         Definitions.Prod t2 t3 -> Definitions.Prod (dt t2) (dt t3);
         Definitions.Sum t2 t3 -> Definitions.Sum (dt t2) (dt t3)}}
     in dt _UU03c3_)
    (coq_Dtm _UU0393_ (Definitions.Arrow _UU03c3_ _UU03c4_) t0)
    (coq_Dtm _UU0393_ _UU03c3_ t1);
   Definitions.Coq_abs _UU03c4_ _UU03c3_ t0 -> Definitions.Coq_abs
    (coq_Dt _UU03c4_) (coq_Dt _UU03c3_)
    (coq_Dtm (Datatypes.Coq_cons _UU03c3_ _UU0393_) _UU03c4_ t0);
   Definitions.Coq_build _UU03c4_ n t0 -> Definitions.Coq_build
    (coq_Dt _UU03c4_) n (Basics.compose (coq_Dtm _UU0393_ _UU03c4_) t0);
   Definitions.Coq_get _UU03c4_ n t0 t1 -> Definitions.Coq_get
    (let {
      dt _UU03c4_0 =
        case _UU03c4_0 of {
         Definitions.Real -> Definitions.Prod Definitions.Real
          Definitions.Real;
         Definitions.Nat -> Definitions.Nat;
         Definitions.Array n0 t2 -> Definitions.Array n0 (dt t2);
         Definitions.Arrow t2 t3 -> Definitions.Arrow (dt t2) (dt t3);
         Definitions.Prod t2 t3 -> Definitions.Prod (dt t2) (dt t3);
         Definitions.Sum t2 t3 -> Definitions.Sum (dt t2) (dt t3)}}
     in dt _UU03c4_) n t0
    (coq_Dtm _UU0393_ (Definitions.Array n _UU03c4_) t1);
   Definitions.Coq_rval r -> Definitions.Coq_tuple Definitions.Real
    Definitions.Real (Definitions.Coq_rval r) (Definitions.Coq_rval
    (Rdefinitions.coq_IZR BinNums.Z0));
   Definitions.Coq_add t0 t1 ->
    let {refine = coq_Dtm _UU0393_ Definitions.Real t0} in
    let {refine0 = coq_Dtm _UU0393_ Definitions.Real t1} in
    Definitions.Coq_tuple Definitions.Real Definitions.Real
    (Definitions.Coq_add (Definitions.Coq_first Definitions.Real
    Definitions.Real refine) (Definitions.Coq_first Definitions.Real
    Definitions.Real refine0)) (Definitions.Coq_add (Definitions.Coq_second
    Definitions.Real Definitions.Real refine) (Definitions.Coq_second
    Definitions.Real Definitions.Real refine0));
   Definitions.Coq_mul t0 t1 ->
    let {refine = coq_Dtm _UU0393_ Definitions.Real t0} in
    let {refine0 = coq_Dtm _UU0393_ Definitions.Real t1} in
    Definitions.Coq_tuple Definitions.Real Definitions.Real
    (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
    Definitions.Real refine) (Definitions.Coq_first Definitions.Real
    Definitions.Real refine0)) (Definitions.Coq_add (Definitions.Coq_mul
    (Definitions.Coq_first Definitions.Real Definitions.Real refine)
    (Definitions.Coq_second Definitions.Real Definitions.Real refine0))
    (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
    Definitions.Real refine0) (Definitions.Coq_second Definitions.Real
    Definitions.Real refine)));
   Definitions.Coq_nsucc t0 -> Definitions.Coq_nsucc
    (coq_Dtm _UU0393_ Definitions.Nat t0);
   Definitions.Coq_nval n -> Definitions.Coq_nval n;
   Definitions.Coq_nrec _UU03c4_ t0 t1 t2 -> Definitions.Coq_nrec
    (let {
      dt _UU03c4_0 =
        case _UU03c4_0 of {
         Definitions.Real -> Definitions.Prod Definitions.Real
          Definitions.Real;
         Definitions.Nat -> Definitions.Nat;
         Definitions.Array n t3 -> Definitions.Array n (dt t3);
         Definitions.Arrow t3 t4 -> Definitions.Arrow (dt t3) (dt t4);
         Definitions.Prod t3 t4 -> Definitions.Prod (dt t3) (dt t4);
         Definitions.Sum t3 t4 -> Definitions.Sum (dt t3) (dt t4)}}
     in dt _UU03c4_)
    (coq_Dtm _UU0393_ (Definitions.Arrow _UU03c4_ _UU03c4_) t0)
    (coq_Dtm _UU0393_ Definitions.Nat t1) (coq_Dtm _UU0393_ _UU03c4_ t2);
   Definitions.Coq_tuple _UU03c4_ _UU03c3_ t0 t1 -> Definitions.Coq_tuple
    (coq_Dt _UU03c4_) (coq_Dt _UU03c3_) (coq_Dtm _UU0393_ _UU03c4_ t0)
    (coq_Dtm _UU0393_ _UU03c3_ t1);
   Definitions.Coq_first _UU03c4_ _UU03c3_ t0 -> Definitions.Coq_first
    (let {
      dt _UU03c4_0 =
        case _UU03c4_0 of {
         Definitions.Real -> Definitions.Prod Definitions.Real
          Definitions.Real;
         Definitions.Nat -> Definitions.Nat;
         Definitions.Array n t1 -> Definitions.Array n (dt t1);
         Definitions.Arrow t1 t2 -> Definitions.Arrow (dt t1) (dt t2);
         Definitions.Prod t1 t2 -> Definitions.Prod (dt t1) (dt t2);
         Definitions.Sum t1 t2 -> Definitions.Sum (dt t1) (dt t2)}}
     in dt _UU03c4_)
    (let {
      dt _UU03c4_0 =
        case _UU03c4_0 of {
         Definitions.Real -> Definitions.Prod Definitions.Real
          Definitions.Real;
         Definitions.Nat -> Definitions.Nat;
         Definitions.Array n t1 -> Definitions.Array n (dt t1);
         Definitions.Arrow t1 t2 -> Definitions.Arrow (dt t1) (dt t2);
         Definitions.Prod t1 t2 -> Definitions.Prod (dt t1) (dt t2);
         Definitions.Sum t1 t2 -> Definitions.Sum (dt t1) (dt t2)}}
     in dt _UU03c3_)
    (coq_Dtm _UU0393_ (Definitions.Prod _UU03c4_ _UU03c3_) t0);
   Definitions.Coq_second _UU03c4_ _UU03c3_ t0 -> Definitions.Coq_second
    (let {
      dt _UU03c4_0 =
        case _UU03c4_0 of {
         Definitions.Real -> Definitions.Prod Definitions.Real
          Definitions.Real;
         Definitions.Nat -> Definitions.Nat;
         Definitions.Array n t1 -> Definitions.Array n (dt t1);
         Definitions.Arrow t1 t2 -> Definitions.Arrow (dt t1) (dt t2);
         Definitions.Prod t1 t2 -> Definitions.Prod (dt t1) (dt t2);
         Definitions.Sum t1 t2 -> Definitions.Sum (dt t1) (dt t2)}}
     in dt _UU03c4_)
    (let {
      dt _UU03c4_0 =
        case _UU03c4_0 of {
         Definitions.Real -> Definitions.Prod Definitions.Real
          Definitions.Real;
         Definitions.Nat -> Definitions.Nat;
         Definitions.Array n t1 -> Definitions.Array n (dt t1);
         Definitions.Arrow t1 t2 -> Definitions.Arrow (dt t1) (dt t2);
         Definitions.Prod t1 t2 -> Definitions.Prod (dt t1) (dt t2);
         Definitions.Sum t1 t2 -> Definitions.Sum (dt t1) (dt t2)}}
     in dt _UU03c3_)
    (coq_Dtm _UU0393_ (Definitions.Prod _UU03c4_ _UU03c3_) t0);
   Definitions.Coq_case _UU03c4_ _UU03c3_ _UU03c1_ t0 t1 t2 ->
    Definitions.Coq_case
    (let {
      dt _UU03c4_0 =
        case _UU03c4_0 of {
         Definitions.Real -> Definitions.Prod Definitions.Real
          Definitions.Real;
         Definitions.Nat -> Definitions.Nat;
         Definitions.Array n t3 -> Definitions.Array n (dt t3);
         Definitions.Arrow t3 t4 -> Definitions.Arrow (dt t3) (dt t4);
         Definitions.Prod t3 t4 -> Definitions.Prod (dt t3) (dt t4);
         Definitions.Sum t3 t4 -> Definitions.Sum (dt t3) (dt t4)}}
     in dt _UU03c4_)
    (let {
      dt _UU03c4_0 =
        case _UU03c4_0 of {
         Definitions.Real -> Definitions.Prod Definitions.Real
          Definitions.Real;
         Definitions.Nat -> Definitions.Nat;
         Definitions.Array n t3 -> Definitions.Array n (dt t3);
         Definitions.Arrow t3 t4 -> Definitions.Arrow (dt t3) (dt t4);
         Definitions.Prod t3 t4 -> Definitions.Prod (dt t3) (dt t4);
         Definitions.Sum t3 t4 -> Definitions.Sum (dt t3) (dt t4)}}
     in dt _UU03c3_)
    (let {
      dt _UU03c4_0 =
        case _UU03c4_0 of {
         Definitions.Real -> Definitions.Prod Definitions.Real
          Definitions.Real;
         Definitions.Nat -> Definitions.Nat;
         Definitions.Array n t3 -> Definitions.Array n (dt t3);
         Definitions.Arrow t3 t4 -> Definitions.Arrow (dt t3) (dt t4);
         Definitions.Prod t3 t4 -> Definitions.Prod (dt t3) (dt t4);
         Definitions.Sum t3 t4 -> Definitions.Sum (dt t3) (dt t4)}}
     in dt _UU03c1_)
    (coq_Dtm _UU0393_ (Definitions.Sum _UU03c4_ _UU03c3_) t0)
    (coq_Dtm _UU0393_ (Definitions.Arrow _UU03c4_ _UU03c1_) t1)
    (coq_Dtm _UU0393_ (Definitions.Arrow _UU03c3_ _UU03c1_) t2);
   Definitions.Coq_inl _UU03c4_ _UU03c3_ t0 -> Definitions.Coq_inl
    (coq_Dt _UU03c4_)
    (let {
      dt _UU03c4_0 =
        case _UU03c4_0 of {
         Definitions.Real -> Definitions.Prod Definitions.Real
          Definitions.Real;
         Definitions.Nat -> Definitions.Nat;
         Definitions.Array n t1 -> Definitions.Array n (dt t1);
         Definitions.Arrow t1 t2 -> Definitions.Arrow (dt t1) (dt t2);
         Definitions.Prod t1 t2 -> Definitions.Prod (dt t1) (dt t2);
         Definitions.Sum t1 t2 -> Definitions.Sum (dt t1) (dt t2)}}
     in dt _UU03c3_) (coq_Dtm _UU0393_ _UU03c4_ t0);
   Definitions.Coq_inr _UU03c4_ _UU03c3_ t0 -> Definitions.Coq_inr
    (let {
      dt _UU03c4_0 =
        case _UU03c4_0 of {
         Definitions.Real -> Definitions.Prod Definitions.Real
          Definitions.Real;
         Definitions.Nat -> Definitions.Nat;
         Definitions.Array n t1 -> Definitions.Array n (dt t1);
         Definitions.Arrow t1 t2 -> Definitions.Arrow (dt t1) (dt t2);
         Definitions.Prod t1 t2 -> Definitions.Prod (dt t1) (dt t2);
         Definitions.Sum t1 t2 -> Definitions.Sum (dt t1) (dt t2)}}
     in dt _UU03c4_) (coq_Dt _UU03c3_) (coq_Dtm _UU0393_ _UU03c3_ t0)}

data Dtm_graph =
   Dtm_graph_equation_1 (Definitions.Ctx Definitions.Coq_ty) Definitions.Coq_ty 
 (Definitions.Var Definitions.Coq_ty)
 | Dtm_graph_equation_2 (Definitions.Ctx Definitions.Coq_ty) Definitions.Coq_ty 
 Definitions.Coq_ty Definitions.Coq_tm Definitions.Coq_tm Dtm_graph Dtm_graph
 | Dtm_graph_equation_3 (Definitions.Ctx Definitions.Coq_ty) Definitions.Coq_ty 
 Definitions.Coq_ty Definitions.Coq_tm Dtm_graph
 | Dtm_graph_equation_4 (Definitions.Ctx Definitions.Coq_ty) Definitions.Coq_ty 
 Datatypes.Coq_nat (Fin.Coq_t -> Definitions.Coq_tm)
 | Dtm_graph_equation_5 (Definitions.Ctx Definitions.Coq_ty) Definitions.Coq_ty 
 Datatypes.Coq_nat Fin.Coq_t Definitions.Coq_tm Dtm_graph
 | Dtm_graph_equation_6 (Definitions.Ctx Definitions.Coq_ty) Rdefinitions.RbaseSymbolsImpl__R
 | Dtm_graph_refinement_7 (Definitions.Ctx Definitions.Coq_ty) Definitions.Coq_tm 
 Definitions.Coq_tm Dtm_graph Dtm_clause_10_graph
 | Dtm_graph_refinement_8 (Definitions.Ctx Definitions.Coq_ty) Definitions.Coq_tm 
 Definitions.Coq_tm Dtm_graph Dtm_clause_11_graph
 | Dtm_graph_equation_9 (Definitions.Ctx Definitions.Coq_ty) Definitions.Coq_tm 
 Dtm_graph
 | Dtm_graph_equation_10 (Definitions.Ctx Definitions.Coq_ty) Datatypes.Coq_nat
 | Dtm_graph_equation_11 (Definitions.Ctx Definitions.Coq_ty) Definitions.Coq_ty 
 Definitions.Coq_tm Definitions.Coq_tm Definitions.Coq_tm Dtm_graph Dtm_graph 
 Dtm_graph
 | Dtm_graph_equation_12 (Definitions.Ctx Definitions.Coq_ty) Definitions.Coq_ty 
 Definitions.Coq_ty Definitions.Coq_tm Definitions.Coq_tm Dtm_graph Dtm_graph
 | Dtm_graph_equation_13 (Definitions.Ctx Definitions.Coq_ty) Definitions.Coq_ty 
 Definitions.Coq_ty Definitions.Coq_tm Dtm_graph
 | Dtm_graph_equation_14 (Definitions.Ctx Definitions.Coq_ty) Definitions.Coq_ty 
 Definitions.Coq_ty Definitions.Coq_tm Dtm_graph
 | Dtm_graph_equation_15 (Definitions.Ctx Definitions.Coq_ty) Definitions.Coq_ty 
 Definitions.Coq_ty Definitions.Coq_ty Definitions.Coq_tm Definitions.Coq_tm 
 Definitions.Coq_tm Dtm_graph Dtm_graph Dtm_graph
 | Dtm_graph_equation_16 (Definitions.Ctx Definitions.Coq_ty) Definitions.Coq_ty 
 Definitions.Coq_ty Definitions.Coq_tm Dtm_graph
 | Dtm_graph_equation_17 (Definitions.Ctx Definitions.Coq_ty) Definitions.Coq_ty 
 Definitions.Coq_ty Definitions.Coq_tm Dtm_graph
data Dtm_clause_10_graph =
   Dtm_clause_10_graph_refinement_1 (Definitions.Ctx Definitions.Coq_ty) 
 Definitions.Coq_tm Definitions.Coq_tm Definitions.Coq_tm Dtm_graph Dtm_clause_10_clause_1_graph
data Dtm_clause_10_clause_1_graph =
   Dtm_clause_10_clause_1_graph_equation_1 (Definitions.Ctx
                                           Definitions.Coq_ty) Definitions.Coq_tm 
 Definitions.Coq_tm Definitions.Coq_tm Definitions.Coq_tm
data Dtm_clause_11_graph =
   Dtm_clause_11_graph_refinement_1 (Definitions.Ctx Definitions.Coq_ty) 
 Definitions.Coq_tm Definitions.Coq_tm Definitions.Coq_tm Dtm_graph Dtm_clause_11_clause_1_graph
data Dtm_clause_11_clause_1_graph =
   Dtm_clause_11_clause_1_graph_equation_1 (Definitions.Ctx
                                           Definitions.Coq_ty) Definitions.Coq_tm 
 Definitions.Coq_tm Definitions.Coq_tm Definitions.Coq_tm

coq_Dtm_clause_11_clause_1_graph_mut :: ((Definitions.Ctx Definitions.Coq_ty)
                                        -> Definitions.Coq_ty ->
                                        (Definitions.Var Definitions.Coq_ty)
                                        -> a1) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> Dtm_graph -> a1 -> a1) ->
                                        ((Definitions.Ctx Definitions.Coq_ty)
                                        -> Definitions.Coq_ty ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> a1) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_ty ->
                                        Datatypes.Coq_nat -> (Fin.Coq_t ->
                                        Definitions.Coq_tm) -> a1) ->
                                        ((Definitions.Ctx Definitions.Coq_ty)
                                        -> Definitions.Coq_ty ->
                                        Datatypes.Coq_nat -> Fin.Coq_t ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> a1) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Rdefinitions.RbaseSymbolsImpl__R ->
                                        a1) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> Dtm_clause_10_graph -> a2 -> a1)
                                        -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> Dtm_clause_11_graph -> a4 -> a1)
                                        -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> a1) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Datatypes.Coq_nat -> a1) ->
                                        ((Definitions.Ctx Definitions.Coq_ty)
                                        -> Definitions.Coq_ty ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> Dtm_graph -> a1 -> Dtm_graph -> a1
                                        -> a1) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> Dtm_graph -> a1 -> a1) ->
                                        ((Definitions.Ctx Definitions.Coq_ty)
                                        -> Definitions.Coq_ty ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> a1) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> a1) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> Dtm_graph -> a1 -> Dtm_graph -> a1
                                        -> a1) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> a1) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> a1) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> Dtm_clause_10_clause_1_graph -> a3
                                        -> a2) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm -> a3) ->
                                        ((Definitions.Ctx Definitions.Coq_ty)
                                        -> Definitions.Coq_tm ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> Dtm_clause_11_clause_1_graph -> a5
                                        -> a4) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm -> a5) ->
                                        (Definitions.Ctx Definitions.Coq_ty)
                                        -> Definitions.Coq_tm ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm ->
                                        Dtm_clause_11_clause_1_graph -> a5
coq_Dtm_clause_11_clause_1_graph_mut _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f _ _ _ _ _ _ d =
  case d of {
   Dtm_clause_11_clause_1_graph_equation_1 _UU0393_ t8 refine0 t7 refine ->
    f _UU0393_ t8 refine0 t7 refine}

coq_Dtm_clause_11_graph_mut :: ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_ty -> (Definitions.Var
                               Definitions.Coq_ty) -> a1) ->
                               ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_ty -> Definitions.Coq_ty ->
                               Definitions.Coq_tm -> Definitions.Coq_tm ->
                               Dtm_graph -> a1 -> Dtm_graph -> a1 -> a1) ->
                               ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_ty -> Definitions.Coq_ty ->
                               Definitions.Coq_tm -> Dtm_graph -> a1 -> a1)
                               -> ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_ty -> Datatypes.Coq_nat ->
                               (Fin.Coq_t -> Definitions.Coq_tm) -> a1) ->
                               ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_ty -> Datatypes.Coq_nat ->
                               Fin.Coq_t -> Definitions.Coq_tm -> Dtm_graph
                               -> a1 -> a1) -> ((Definitions.Ctx
                               Definitions.Coq_ty) ->
                               Rdefinitions.RbaseSymbolsImpl__R -> a1) ->
                               ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_tm -> Definitions.Coq_tm ->
                               Dtm_graph -> a1 -> Dtm_clause_10_graph -> a2
                               -> a1) -> ((Definitions.Ctx
                               Definitions.Coq_ty) -> Definitions.Coq_tm ->
                               Definitions.Coq_tm -> Dtm_graph -> a1 ->
                               Dtm_clause_11_graph -> a4 -> a1) ->
                               ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_tm -> Dtm_graph -> a1 -> a1)
                               -> ((Definitions.Ctx Definitions.Coq_ty) ->
                               Datatypes.Coq_nat -> a1) -> ((Definitions.Ctx
                               Definitions.Coq_ty) -> Definitions.Coq_ty ->
                               Definitions.Coq_tm -> Definitions.Coq_tm ->
                               Definitions.Coq_tm -> Dtm_graph -> a1 ->
                               Dtm_graph -> a1 -> Dtm_graph -> a1 -> a1) ->
                               ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_ty -> Definitions.Coq_ty ->
                               Definitions.Coq_tm -> Definitions.Coq_tm ->
                               Dtm_graph -> a1 -> Dtm_graph -> a1 -> a1) ->
                               ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_ty -> Definitions.Coq_ty ->
                               Definitions.Coq_tm -> Dtm_graph -> a1 -> a1)
                               -> ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_ty -> Definitions.Coq_ty ->
                               Definitions.Coq_tm -> Dtm_graph -> a1 -> a1)
                               -> ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_ty -> Definitions.Coq_ty ->
                               Definitions.Coq_ty -> Definitions.Coq_tm ->
                               Definitions.Coq_tm -> Definitions.Coq_tm ->
                               Dtm_graph -> a1 -> Dtm_graph -> a1 ->
                               Dtm_graph -> a1 -> a1) -> ((Definitions.Ctx
                               Definitions.Coq_ty) -> Definitions.Coq_ty ->
                               Definitions.Coq_ty -> Definitions.Coq_tm ->
                               Dtm_graph -> a1 -> a1) -> ((Definitions.Ctx
                               Definitions.Coq_ty) -> Definitions.Coq_ty ->
                               Definitions.Coq_ty -> Definitions.Coq_tm ->
                               Dtm_graph -> a1 -> a1) -> ((Definitions.Ctx
                               Definitions.Coq_ty) -> Definitions.Coq_tm ->
                               Definitions.Coq_tm -> Definitions.Coq_tm ->
                               Dtm_graph -> a1 ->
                               Dtm_clause_10_clause_1_graph -> a3 -> a2) ->
                               ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_tm -> Definitions.Coq_tm ->
                               Definitions.Coq_tm -> Definitions.Coq_tm ->
                               a3) -> ((Definitions.Ctx Definitions.Coq_ty)
                               -> Definitions.Coq_tm -> Definitions.Coq_tm ->
                               Definitions.Coq_tm -> Dtm_graph -> a1 ->
                               Dtm_clause_11_clause_1_graph -> a5 -> a4) ->
                               ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_tm -> Definitions.Coq_tm ->
                               Definitions.Coq_tm -> Definitions.Coq_tm ->
                               a5) -> (Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_tm -> Definitions.Coq_tm ->
                               Definitions.Coq_tm -> Definitions.Coq_tm ->
                               Dtm_clause_11_graph -> a4
coq_Dtm_clause_11_graph_mut f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 =
  let {
   f20 _ _ _ _ d =
     case d of {
      Dtm_graph_equation_1 _UU0393_ _UU03c4_0 v -> f _UU0393_ _UU03c4_0 v;
      Dtm_graph_equation_2 _UU0393_ _UU03c4_1 _UU03c3_ t t0 hind hind0 ->
       f0 _UU0393_ _UU03c4_1 _UU03c3_ t t0 hind
         (f20 _UU0393_ (Definitions.Arrow _UU03c3_ _UU03c4_1) t
           (coq_Dtm _UU0393_ (Definitions.Arrow _UU03c3_ _UU03c4_1) t) hind)
         hind0
         (f20 _UU0393_ _UU03c3_ t0 (coq_Dtm _UU0393_ _UU03c3_ t0) hind0);
      Dtm_graph_equation_3 _UU0393_ _UU03c4_2 _UU03c3_0 t1 hind ->
       f1 _UU0393_ _UU03c4_2 _UU03c3_0 t1 hind
         (f20 (Datatypes.Coq_cons _UU03c3_0 _UU0393_) _UU03c4_2 t1
           (coq_Dtm (Datatypes.Coq_cons _UU03c3_0 _UU0393_) _UU03c4_2 t1)
           hind);
      Dtm_graph_equation_4 _UU0393_ _UU03c4_3 n t2 ->
       f2 _UU0393_ _UU03c4_3 n t2;
      Dtm_graph_equation_5 _UU0393_ _UU03c4_4 n0 t3 t4 hind ->
       f3 _UU0393_ _UU03c4_4 n0 t3 t4 hind
         (f20 _UU0393_ (Definitions.Array n0 _UU03c4_4) t4
           (coq_Dtm _UU0393_ (Definitions.Array n0 _UU03c4_4) t4) hind);
      Dtm_graph_equation_6 _UU0393_ r -> f4 _UU0393_ r;
      Dtm_graph_refinement_7 _UU0393_ t5 t6 hind hind0 ->
       f5 _UU0393_ t5 t6 hind
         (f20 _UU0393_ Definitions.Real t5
           (coq_Dtm _UU0393_ Definitions.Real t5) hind) hind0
         (f21 _UU0393_ t5 (coq_Dtm _UU0393_ Definitions.Real t5) t6
           (let {refine = coq_Dtm _UU0393_ Definitions.Real t5} in
            let {refine0 = coq_Dtm _UU0393_ Definitions.Real t6} in
            Definitions.Coq_tuple Definitions.Real Definitions.Real
            (Definitions.Coq_add (Definitions.Coq_first Definitions.Real
            Definitions.Real refine) (Definitions.Coq_first Definitions.Real
            Definitions.Real refine0)) (Definitions.Coq_add
            (Definitions.Coq_second Definitions.Real Definitions.Real refine)
            (Definitions.Coq_second Definitions.Real Definitions.Real
            refine0))) hind0);
      Dtm_graph_refinement_8 _UU0393_ t7 t8 hind hind0 ->
       f6 _UU0393_ t7 t8 hind
         (f20 _UU0393_ Definitions.Real t7
           (coq_Dtm _UU0393_ Definitions.Real t7) hind) hind0
         (f23 _UU0393_ t7 (coq_Dtm _UU0393_ Definitions.Real t7) t8
           (let {refine = coq_Dtm _UU0393_ Definitions.Real t7} in
            let {refine0 = coq_Dtm _UU0393_ Definitions.Real t8} in
            Definitions.Coq_tuple Definitions.Real Definitions.Real
            (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
            Definitions.Real refine) (Definitions.Coq_first Definitions.Real
            Definitions.Real refine0)) (Definitions.Coq_add
            (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
            Definitions.Real refine) (Definitions.Coq_second Definitions.Real
            Definitions.Real refine0)) (Definitions.Coq_mul
            (Definitions.Coq_first Definitions.Real Definitions.Real refine0)
            (Definitions.Coq_second Definitions.Real Definitions.Real
            refine)))) hind0);
      Dtm_graph_equation_9 _UU0393_ t9 hind ->
       f7 _UU0393_ t9 hind
         (f20 _UU0393_ Definitions.Nat t9
           (coq_Dtm _UU0393_ Definitions.Nat t9) hind);
      Dtm_graph_equation_10 _UU0393_ n1 -> f8 _UU0393_ n1;
      Dtm_graph_equation_11 _UU0393_ _UU03c4_5 t10 t11 t12 hind hind0
       hind1 ->
       f9 _UU0393_ _UU03c4_5 t10 t11 t12 hind
         (f20 _UU0393_ (Definitions.Arrow _UU03c4_5 _UU03c4_5) t10
           (coq_Dtm _UU0393_ (Definitions.Arrow _UU03c4_5 _UU03c4_5) t10)
           hind) hind0
         (f20 _UU0393_ Definitions.Nat t11
           (coq_Dtm _UU0393_ Definitions.Nat t11) hind0) hind1
         (f20 _UU0393_ _UU03c4_5 t12 (coq_Dtm _UU0393_ _UU03c4_5 t12) hind1);
      Dtm_graph_equation_12 _UU0393_ _UU03c4_6 _UU03c3_1 t13 t14 hind
       hind0 ->
       f10 _UU0393_ _UU03c4_6 _UU03c3_1 t13 t14 hind
         (f20 _UU0393_ _UU03c4_6 t13 (coq_Dtm _UU0393_ _UU03c4_6 t13) hind)
         hind0
         (f20 _UU0393_ _UU03c3_1 t14 (coq_Dtm _UU0393_ _UU03c3_1 t14) hind0);
      Dtm_graph_equation_13 _UU0393_ _UU03c4_7 _UU03c3_2 t15 hind ->
       f11 _UU0393_ _UU03c4_7 _UU03c3_2 t15 hind
         (f20 _UU0393_ (Definitions.Prod _UU03c4_7 _UU03c3_2) t15
           (coq_Dtm _UU0393_ (Definitions.Prod _UU03c4_7 _UU03c3_2) t15)
           hind);
      Dtm_graph_equation_14 _UU0393_ _UU03c3_3 _UU03c4_8 t16 hind ->
       f12 _UU0393_ _UU03c3_3 _UU03c4_8 t16 hind
         (f20 _UU0393_ (Definitions.Prod _UU03c4_8 _UU03c3_3) t16
           (coq_Dtm _UU0393_ (Definitions.Prod _UU03c4_8 _UU03c3_3) t16)
           hind);
      Dtm_graph_equation_15 _UU0393_ _UU03c1_ _UU03c4_9 _UU03c3_4 t17 t18 t19
       hind hind0 hind1 ->
       f13 _UU0393_ _UU03c1_ _UU03c4_9 _UU03c3_4 t17 t18 t19 hind
         (f20 _UU0393_ (Definitions.Sum _UU03c4_9 _UU03c3_4) t17
           (coq_Dtm _UU0393_ (Definitions.Sum _UU03c4_9 _UU03c3_4) t17) hind)
         hind0
         (f20 _UU0393_ (Definitions.Arrow _UU03c4_9 _UU03c1_) t18
           (coq_Dtm _UU0393_ (Definitions.Arrow _UU03c4_9 _UU03c1_) t18)
           hind0) hind1
         (f20 _UU0393_ (Definitions.Arrow _UU03c3_4 _UU03c1_) t19
           (coq_Dtm _UU0393_ (Definitions.Arrow _UU03c3_4 _UU03c1_) t19)
           hind1);
      Dtm_graph_equation_16 _UU0393_ _UU03c4_10 _UU03c3_5 t20 hind ->
       f14 _UU0393_ _UU03c4_10 _UU03c3_5 t20 hind
         (f20 _UU0393_ _UU03c4_10 t20 (coq_Dtm _UU0393_ _UU03c4_10 t20) hind);
      Dtm_graph_equation_17 _UU0393_ _UU03c4_11 _UU03c3_6 t21 hind ->
       f15 _UU0393_ _UU03c4_11 _UU03c3_6 t21 hind
         (f20 _UU0393_ _UU03c3_6 t21 (coq_Dtm _UU0393_ _UU03c3_6 t21) hind)};
   f21 _ _ _ _ _ d =
     case d of {
      Dtm_clause_10_graph_refinement_1 _UU0393_ t5 refine t6 hind hind0 ->
       f16 _UU0393_ t5 refine t6 hind
         (f20 _UU0393_ Definitions.Real t6
           (coq_Dtm _UU0393_ Definitions.Real t6) hind) hind0
         (f22 _UU0393_ t6 (coq_Dtm _UU0393_ Definitions.Real t6) t5 refine
           (let {refine0 = coq_Dtm _UU0393_ Definitions.Real t6} in
            Definitions.Coq_tuple Definitions.Real Definitions.Real
            (Definitions.Coq_add (Definitions.Coq_first Definitions.Real
            Definitions.Real refine) (Definitions.Coq_first Definitions.Real
            Definitions.Real refine0)) (Definitions.Coq_add
            (Definitions.Coq_second Definitions.Real Definitions.Real refine)
            (Definitions.Coq_second Definitions.Real Definitions.Real
            refine0))) hind0)};
   f22 _ _ _ _ _ _ d =
     case d of {
      Dtm_clause_10_clause_1_graph_equation_1 _UU0393_ t6 refine0 t5
       refine -> f17 _UU0393_ t6 refine0 t5 refine};
   f23 _ _ _ _ _ d =
     case d of {
      Dtm_clause_11_graph_refinement_1 _UU0393_ t7 refine t8 hind hind0 ->
       f18 _UU0393_ t7 refine t8 hind
         (f20 _UU0393_ Definitions.Real t8
           (coq_Dtm _UU0393_ Definitions.Real t8) hind) hind0
         (f24 _UU0393_ t8 (coq_Dtm _UU0393_ Definitions.Real t8) t7 refine
           (let {refine0 = coq_Dtm _UU0393_ Definitions.Real t8} in
            Definitions.Coq_tuple Definitions.Real Definitions.Real
            (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
            Definitions.Real refine) (Definitions.Coq_first Definitions.Real
            Definitions.Real refine0)) (Definitions.Coq_add
            (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
            Definitions.Real refine) (Definitions.Coq_second Definitions.Real
            Definitions.Real refine0)) (Definitions.Coq_mul
            (Definitions.Coq_first Definitions.Real Definitions.Real refine0)
            (Definitions.Coq_second Definitions.Real Definitions.Real
            refine)))) hind0)};
   f24 _ _ _ _ _ _ d =
     case d of {
      Dtm_clause_11_clause_1_graph_equation_1 _UU0393_ t8 refine0 t7
       refine -> f19 _UU0393_ t8 refine0 t7 refine}}
  in f23

coq_Dtm_clause_10_clause_1_graph_mut :: ((Definitions.Ctx Definitions.Coq_ty)
                                        -> Definitions.Coq_ty ->
                                        (Definitions.Var Definitions.Coq_ty)
                                        -> a1) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> Dtm_graph -> a1 -> a1) ->
                                        ((Definitions.Ctx Definitions.Coq_ty)
                                        -> Definitions.Coq_ty ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> a1) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_ty ->
                                        Datatypes.Coq_nat -> (Fin.Coq_t ->
                                        Definitions.Coq_tm) -> a1) ->
                                        ((Definitions.Ctx Definitions.Coq_ty)
                                        -> Definitions.Coq_ty ->
                                        Datatypes.Coq_nat -> Fin.Coq_t ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> a1) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Rdefinitions.RbaseSymbolsImpl__R ->
                                        a1) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> Dtm_clause_10_graph -> a2 -> a1)
                                        -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> Dtm_clause_11_graph -> a4 -> a1)
                                        -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> a1) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Datatypes.Coq_nat -> a1) ->
                                        ((Definitions.Ctx Definitions.Coq_ty)
                                        -> Definitions.Coq_ty ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> Dtm_graph -> a1 -> Dtm_graph -> a1
                                        -> a1) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> Dtm_graph -> a1 -> a1) ->
                                        ((Definitions.Ctx Definitions.Coq_ty)
                                        -> Definitions.Coq_ty ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> a1) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> a1) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> Dtm_graph -> a1 -> Dtm_graph -> a1
                                        -> a1) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> a1) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_ty ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> a1) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> Dtm_clause_10_clause_1_graph -> a3
                                        -> a2) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm -> a3) ->
                                        ((Definitions.Ctx Definitions.Coq_ty)
                                        -> Definitions.Coq_tm ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm -> Dtm_graph -> a1
                                        -> Dtm_clause_11_clause_1_graph -> a5
                                        -> a4) -> ((Definitions.Ctx
                                        Definitions.Coq_ty) ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm -> a5) ->
                                        (Definitions.Ctx Definitions.Coq_ty)
                                        -> Definitions.Coq_tm ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm ->
                                        Definitions.Coq_tm ->
                                        Dtm_clause_10_clause_1_graph -> a3
coq_Dtm_clause_10_clause_1_graph_mut _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f _ _ _ _ _ _ _ _ d =
  case d of {
   Dtm_clause_10_clause_1_graph_equation_1 _UU0393_ t6 refine0 t5 refine ->
    f _UU0393_ t6 refine0 t5 refine}

coq_Dtm_clause_10_graph_mut :: ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_ty -> (Definitions.Var
                               Definitions.Coq_ty) -> a1) ->
                               ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_ty -> Definitions.Coq_ty ->
                               Definitions.Coq_tm -> Definitions.Coq_tm ->
                               Dtm_graph -> a1 -> Dtm_graph -> a1 -> a1) ->
                               ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_ty -> Definitions.Coq_ty ->
                               Definitions.Coq_tm -> Dtm_graph -> a1 -> a1)
                               -> ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_ty -> Datatypes.Coq_nat ->
                               (Fin.Coq_t -> Definitions.Coq_tm) -> a1) ->
                               ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_ty -> Datatypes.Coq_nat ->
                               Fin.Coq_t -> Definitions.Coq_tm -> Dtm_graph
                               -> a1 -> a1) -> ((Definitions.Ctx
                               Definitions.Coq_ty) ->
                               Rdefinitions.RbaseSymbolsImpl__R -> a1) ->
                               ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_tm -> Definitions.Coq_tm ->
                               Dtm_graph -> a1 -> Dtm_clause_10_graph -> a2
                               -> a1) -> ((Definitions.Ctx
                               Definitions.Coq_ty) -> Definitions.Coq_tm ->
                               Definitions.Coq_tm -> Dtm_graph -> a1 ->
                               Dtm_clause_11_graph -> a4 -> a1) ->
                               ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_tm -> Dtm_graph -> a1 -> a1)
                               -> ((Definitions.Ctx Definitions.Coq_ty) ->
                               Datatypes.Coq_nat -> a1) -> ((Definitions.Ctx
                               Definitions.Coq_ty) -> Definitions.Coq_ty ->
                               Definitions.Coq_tm -> Definitions.Coq_tm ->
                               Definitions.Coq_tm -> Dtm_graph -> a1 ->
                               Dtm_graph -> a1 -> Dtm_graph -> a1 -> a1) ->
                               ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_ty -> Definitions.Coq_ty ->
                               Definitions.Coq_tm -> Definitions.Coq_tm ->
                               Dtm_graph -> a1 -> Dtm_graph -> a1 -> a1) ->
                               ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_ty -> Definitions.Coq_ty ->
                               Definitions.Coq_tm -> Dtm_graph -> a1 -> a1)
                               -> ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_ty -> Definitions.Coq_ty ->
                               Definitions.Coq_tm -> Dtm_graph -> a1 -> a1)
                               -> ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_ty -> Definitions.Coq_ty ->
                               Definitions.Coq_ty -> Definitions.Coq_tm ->
                               Definitions.Coq_tm -> Definitions.Coq_tm ->
                               Dtm_graph -> a1 -> Dtm_graph -> a1 ->
                               Dtm_graph -> a1 -> a1) -> ((Definitions.Ctx
                               Definitions.Coq_ty) -> Definitions.Coq_ty ->
                               Definitions.Coq_ty -> Definitions.Coq_tm ->
                               Dtm_graph -> a1 -> a1) -> ((Definitions.Ctx
                               Definitions.Coq_ty) -> Definitions.Coq_ty ->
                               Definitions.Coq_ty -> Definitions.Coq_tm ->
                               Dtm_graph -> a1 -> a1) -> ((Definitions.Ctx
                               Definitions.Coq_ty) -> Definitions.Coq_tm ->
                               Definitions.Coq_tm -> Definitions.Coq_tm ->
                               Dtm_graph -> a1 ->
                               Dtm_clause_10_clause_1_graph -> a3 -> a2) ->
                               ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_tm -> Definitions.Coq_tm ->
                               Definitions.Coq_tm -> Definitions.Coq_tm ->
                               a3) -> ((Definitions.Ctx Definitions.Coq_ty)
                               -> Definitions.Coq_tm -> Definitions.Coq_tm ->
                               Definitions.Coq_tm -> Dtm_graph -> a1 ->
                               Dtm_clause_11_clause_1_graph -> a5 -> a4) ->
                               ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_tm -> Definitions.Coq_tm ->
                               Definitions.Coq_tm -> Definitions.Coq_tm ->
                               a5) -> (Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_tm -> Definitions.Coq_tm ->
                               Definitions.Coq_tm -> Definitions.Coq_tm ->
                               Dtm_clause_10_graph -> a2
coq_Dtm_clause_10_graph_mut f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 =
  let {
   f20 _ _ _ _ d =
     case d of {
      Dtm_graph_equation_1 _UU0393_ _UU03c4_0 v -> f _UU0393_ _UU03c4_0 v;
      Dtm_graph_equation_2 _UU0393_ _UU03c4_1 _UU03c3_ t t0 hind hind0 ->
       f0 _UU0393_ _UU03c4_1 _UU03c3_ t t0 hind
         (f20 _UU0393_ (Definitions.Arrow _UU03c3_ _UU03c4_1) t
           (coq_Dtm _UU0393_ (Definitions.Arrow _UU03c3_ _UU03c4_1) t) hind)
         hind0
         (f20 _UU0393_ _UU03c3_ t0 (coq_Dtm _UU0393_ _UU03c3_ t0) hind0);
      Dtm_graph_equation_3 _UU0393_ _UU03c4_2 _UU03c3_0 t1 hind ->
       f1 _UU0393_ _UU03c4_2 _UU03c3_0 t1 hind
         (f20 (Datatypes.Coq_cons _UU03c3_0 _UU0393_) _UU03c4_2 t1
           (coq_Dtm (Datatypes.Coq_cons _UU03c3_0 _UU0393_) _UU03c4_2 t1)
           hind);
      Dtm_graph_equation_4 _UU0393_ _UU03c4_3 n t2 ->
       f2 _UU0393_ _UU03c4_3 n t2;
      Dtm_graph_equation_5 _UU0393_ _UU03c4_4 n0 t3 t4 hind ->
       f3 _UU0393_ _UU03c4_4 n0 t3 t4 hind
         (f20 _UU0393_ (Definitions.Array n0 _UU03c4_4) t4
           (coq_Dtm _UU0393_ (Definitions.Array n0 _UU03c4_4) t4) hind);
      Dtm_graph_equation_6 _UU0393_ r -> f4 _UU0393_ r;
      Dtm_graph_refinement_7 _UU0393_ t5 t6 hind hind0 ->
       f5 _UU0393_ t5 t6 hind
         (f20 _UU0393_ Definitions.Real t5
           (coq_Dtm _UU0393_ Definitions.Real t5) hind) hind0
         (f21 _UU0393_ t5 (coq_Dtm _UU0393_ Definitions.Real t5) t6
           (let {refine = coq_Dtm _UU0393_ Definitions.Real t5} in
            let {refine0 = coq_Dtm _UU0393_ Definitions.Real t6} in
            Definitions.Coq_tuple Definitions.Real Definitions.Real
            (Definitions.Coq_add (Definitions.Coq_first Definitions.Real
            Definitions.Real refine) (Definitions.Coq_first Definitions.Real
            Definitions.Real refine0)) (Definitions.Coq_add
            (Definitions.Coq_second Definitions.Real Definitions.Real refine)
            (Definitions.Coq_second Definitions.Real Definitions.Real
            refine0))) hind0);
      Dtm_graph_refinement_8 _UU0393_ t7 t8 hind hind0 ->
       f6 _UU0393_ t7 t8 hind
         (f20 _UU0393_ Definitions.Real t7
           (coq_Dtm _UU0393_ Definitions.Real t7) hind) hind0
         (f23 _UU0393_ t7 (coq_Dtm _UU0393_ Definitions.Real t7) t8
           (let {refine = coq_Dtm _UU0393_ Definitions.Real t7} in
            let {refine0 = coq_Dtm _UU0393_ Definitions.Real t8} in
            Definitions.Coq_tuple Definitions.Real Definitions.Real
            (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
            Definitions.Real refine) (Definitions.Coq_first Definitions.Real
            Definitions.Real refine0)) (Definitions.Coq_add
            (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
            Definitions.Real refine) (Definitions.Coq_second Definitions.Real
            Definitions.Real refine0)) (Definitions.Coq_mul
            (Definitions.Coq_first Definitions.Real Definitions.Real refine0)
            (Definitions.Coq_second Definitions.Real Definitions.Real
            refine)))) hind0);
      Dtm_graph_equation_9 _UU0393_ t9 hind ->
       f7 _UU0393_ t9 hind
         (f20 _UU0393_ Definitions.Nat t9
           (coq_Dtm _UU0393_ Definitions.Nat t9) hind);
      Dtm_graph_equation_10 _UU0393_ n1 -> f8 _UU0393_ n1;
      Dtm_graph_equation_11 _UU0393_ _UU03c4_5 t10 t11 t12 hind hind0
       hind1 ->
       f9 _UU0393_ _UU03c4_5 t10 t11 t12 hind
         (f20 _UU0393_ (Definitions.Arrow _UU03c4_5 _UU03c4_5) t10
           (coq_Dtm _UU0393_ (Definitions.Arrow _UU03c4_5 _UU03c4_5) t10)
           hind) hind0
         (f20 _UU0393_ Definitions.Nat t11
           (coq_Dtm _UU0393_ Definitions.Nat t11) hind0) hind1
         (f20 _UU0393_ _UU03c4_5 t12 (coq_Dtm _UU0393_ _UU03c4_5 t12) hind1);
      Dtm_graph_equation_12 _UU0393_ _UU03c4_6 _UU03c3_1 t13 t14 hind
       hind0 ->
       f10 _UU0393_ _UU03c4_6 _UU03c3_1 t13 t14 hind
         (f20 _UU0393_ _UU03c4_6 t13 (coq_Dtm _UU0393_ _UU03c4_6 t13) hind)
         hind0
         (f20 _UU0393_ _UU03c3_1 t14 (coq_Dtm _UU0393_ _UU03c3_1 t14) hind0);
      Dtm_graph_equation_13 _UU0393_ _UU03c4_7 _UU03c3_2 t15 hind ->
       f11 _UU0393_ _UU03c4_7 _UU03c3_2 t15 hind
         (f20 _UU0393_ (Definitions.Prod _UU03c4_7 _UU03c3_2) t15
           (coq_Dtm _UU0393_ (Definitions.Prod _UU03c4_7 _UU03c3_2) t15)
           hind);
      Dtm_graph_equation_14 _UU0393_ _UU03c3_3 _UU03c4_8 t16 hind ->
       f12 _UU0393_ _UU03c3_3 _UU03c4_8 t16 hind
         (f20 _UU0393_ (Definitions.Prod _UU03c4_8 _UU03c3_3) t16
           (coq_Dtm _UU0393_ (Definitions.Prod _UU03c4_8 _UU03c3_3) t16)
           hind);
      Dtm_graph_equation_15 _UU0393_ _UU03c1_ _UU03c4_9 _UU03c3_4 t17 t18 t19
       hind hind0 hind1 ->
       f13 _UU0393_ _UU03c1_ _UU03c4_9 _UU03c3_4 t17 t18 t19 hind
         (f20 _UU0393_ (Definitions.Sum _UU03c4_9 _UU03c3_4) t17
           (coq_Dtm _UU0393_ (Definitions.Sum _UU03c4_9 _UU03c3_4) t17) hind)
         hind0
         (f20 _UU0393_ (Definitions.Arrow _UU03c4_9 _UU03c1_) t18
           (coq_Dtm _UU0393_ (Definitions.Arrow _UU03c4_9 _UU03c1_) t18)
           hind0) hind1
         (f20 _UU0393_ (Definitions.Arrow _UU03c3_4 _UU03c1_) t19
           (coq_Dtm _UU0393_ (Definitions.Arrow _UU03c3_4 _UU03c1_) t19)
           hind1);
      Dtm_graph_equation_16 _UU0393_ _UU03c4_10 _UU03c3_5 t20 hind ->
       f14 _UU0393_ _UU03c4_10 _UU03c3_5 t20 hind
         (f20 _UU0393_ _UU03c4_10 t20 (coq_Dtm _UU0393_ _UU03c4_10 t20) hind);
      Dtm_graph_equation_17 _UU0393_ _UU03c4_11 _UU03c3_6 t21 hind ->
       f15 _UU0393_ _UU03c4_11 _UU03c3_6 t21 hind
         (f20 _UU0393_ _UU03c3_6 t21 (coq_Dtm _UU0393_ _UU03c3_6 t21) hind)};
   f21 _ _ _ _ _ d =
     case d of {
      Dtm_clause_10_graph_refinement_1 _UU0393_ t5 refine t6 hind hind0 ->
       f16 _UU0393_ t5 refine t6 hind
         (f20 _UU0393_ Definitions.Real t6
           (coq_Dtm _UU0393_ Definitions.Real t6) hind) hind0
         (f22 _UU0393_ t6 (coq_Dtm _UU0393_ Definitions.Real t6) t5 refine
           (let {refine0 = coq_Dtm _UU0393_ Definitions.Real t6} in
            Definitions.Coq_tuple Definitions.Real Definitions.Real
            (Definitions.Coq_add (Definitions.Coq_first Definitions.Real
            Definitions.Real refine) (Definitions.Coq_first Definitions.Real
            Definitions.Real refine0)) (Definitions.Coq_add
            (Definitions.Coq_second Definitions.Real Definitions.Real refine)
            (Definitions.Coq_second Definitions.Real Definitions.Real
            refine0))) hind0)};
   f22 _ _ _ _ _ _ d =
     case d of {
      Dtm_clause_10_clause_1_graph_equation_1 _UU0393_ t6 refine0 t5
       refine -> f17 _UU0393_ t6 refine0 t5 refine};
   f23 _ _ _ _ _ d =
     case d of {
      Dtm_clause_11_graph_refinement_1 _UU0393_ t7 refine t8 hind hind0 ->
       f18 _UU0393_ t7 refine t8 hind
         (f20 _UU0393_ Definitions.Real t8
           (coq_Dtm _UU0393_ Definitions.Real t8) hind) hind0
         (f24 _UU0393_ t8 (coq_Dtm _UU0393_ Definitions.Real t8) t7 refine
           (let {refine0 = coq_Dtm _UU0393_ Definitions.Real t8} in
            Definitions.Coq_tuple Definitions.Real Definitions.Real
            (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
            Definitions.Real refine) (Definitions.Coq_first Definitions.Real
            Definitions.Real refine0)) (Definitions.Coq_add
            (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
            Definitions.Real refine) (Definitions.Coq_second Definitions.Real
            Definitions.Real refine0)) (Definitions.Coq_mul
            (Definitions.Coq_first Definitions.Real Definitions.Real refine0)
            (Definitions.Coq_second Definitions.Real Definitions.Real
            refine)))) hind0)};
   f24 _ _ _ _ _ _ d =
     case d of {
      Dtm_clause_11_clause_1_graph_equation_1 _UU0393_ t8 refine0 t7
       refine -> f19 _UU0393_ t8 refine0 t7 refine}}
  in f21

coq_Dtm_graph_mut :: ((Definitions.Ctx Definitions.Coq_ty) ->
                     Definitions.Coq_ty -> (Definitions.Var
                     Definitions.Coq_ty) -> a1) -> ((Definitions.Ctx
                     Definitions.Coq_ty) -> Definitions.Coq_ty ->
                     Definitions.Coq_ty -> Definitions.Coq_tm ->
                     Definitions.Coq_tm -> Dtm_graph -> a1 -> Dtm_graph -> a1
                     -> a1) -> ((Definitions.Ctx Definitions.Coq_ty) ->
                     Definitions.Coq_ty -> Definitions.Coq_ty ->
                     Definitions.Coq_tm -> Dtm_graph -> a1 -> a1) ->
                     ((Definitions.Ctx Definitions.Coq_ty) ->
                     Definitions.Coq_ty -> Datatypes.Coq_nat -> (Fin.Coq_t ->
                     Definitions.Coq_tm) -> a1) -> ((Definitions.Ctx
                     Definitions.Coq_ty) -> Definitions.Coq_ty ->
                     Datatypes.Coq_nat -> Fin.Coq_t -> Definitions.Coq_tm ->
                     Dtm_graph -> a1 -> a1) -> ((Definitions.Ctx
                     Definitions.Coq_ty) -> Rdefinitions.RbaseSymbolsImpl__R
                     -> a1) -> ((Definitions.Ctx Definitions.Coq_ty) ->
                     Definitions.Coq_tm -> Definitions.Coq_tm -> Dtm_graph ->
                     a1 -> Dtm_clause_10_graph -> a2 -> a1) ->
                     ((Definitions.Ctx Definitions.Coq_ty) ->
                     Definitions.Coq_tm -> Definitions.Coq_tm -> Dtm_graph ->
                     a1 -> Dtm_clause_11_graph -> a4 -> a1) ->
                     ((Definitions.Ctx Definitions.Coq_ty) ->
                     Definitions.Coq_tm -> Dtm_graph -> a1 -> a1) ->
                     ((Definitions.Ctx Definitions.Coq_ty) ->
                     Datatypes.Coq_nat -> a1) -> ((Definitions.Ctx
                     Definitions.Coq_ty) -> Definitions.Coq_ty ->
                     Definitions.Coq_tm -> Definitions.Coq_tm ->
                     Definitions.Coq_tm -> Dtm_graph -> a1 -> Dtm_graph -> a1
                     -> Dtm_graph -> a1 -> a1) -> ((Definitions.Ctx
                     Definitions.Coq_ty) -> Definitions.Coq_ty ->
                     Definitions.Coq_ty -> Definitions.Coq_tm ->
                     Definitions.Coq_tm -> Dtm_graph -> a1 -> Dtm_graph -> a1
                     -> a1) -> ((Definitions.Ctx Definitions.Coq_ty) ->
                     Definitions.Coq_ty -> Definitions.Coq_ty ->
                     Definitions.Coq_tm -> Dtm_graph -> a1 -> a1) ->
                     ((Definitions.Ctx Definitions.Coq_ty) ->
                     Definitions.Coq_ty -> Definitions.Coq_ty ->
                     Definitions.Coq_tm -> Dtm_graph -> a1 -> a1) ->
                     ((Definitions.Ctx Definitions.Coq_ty) ->
                     Definitions.Coq_ty -> Definitions.Coq_ty ->
                     Definitions.Coq_ty -> Definitions.Coq_tm ->
                     Definitions.Coq_tm -> Definitions.Coq_tm -> Dtm_graph ->
                     a1 -> Dtm_graph -> a1 -> Dtm_graph -> a1 -> a1) ->
                     ((Definitions.Ctx Definitions.Coq_ty) ->
                     Definitions.Coq_ty -> Definitions.Coq_ty ->
                     Definitions.Coq_tm -> Dtm_graph -> a1 -> a1) ->
                     ((Definitions.Ctx Definitions.Coq_ty) ->
                     Definitions.Coq_ty -> Definitions.Coq_ty ->
                     Definitions.Coq_tm -> Dtm_graph -> a1 -> a1) ->
                     ((Definitions.Ctx Definitions.Coq_ty) ->
                     Definitions.Coq_tm -> Definitions.Coq_tm ->
                     Definitions.Coq_tm -> Dtm_graph -> a1 ->
                     Dtm_clause_10_clause_1_graph -> a3 -> a2) ->
                     ((Definitions.Ctx Definitions.Coq_ty) ->
                     Definitions.Coq_tm -> Definitions.Coq_tm ->
                     Definitions.Coq_tm -> Definitions.Coq_tm -> a3) ->
                     ((Definitions.Ctx Definitions.Coq_ty) ->
                     Definitions.Coq_tm -> Definitions.Coq_tm ->
                     Definitions.Coq_tm -> Dtm_graph -> a1 ->
                     Dtm_clause_11_clause_1_graph -> a5 -> a4) ->
                     ((Definitions.Ctx Definitions.Coq_ty) ->
                     Definitions.Coq_tm -> Definitions.Coq_tm ->
                     Definitions.Coq_tm -> Definitions.Coq_tm -> a5) ->
                     (Definitions.Ctx Definitions.Coq_ty) ->
                     Definitions.Coq_ty -> Definitions.Coq_tm ->
                     Definitions.Coq_tm -> Dtm_graph -> a1
coq_Dtm_graph_mut f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 =
  let {
   f20 _ _ _ _ d =
     case d of {
      Dtm_graph_equation_1 _UU0393_ _UU03c4_0 v -> f _UU0393_ _UU03c4_0 v;
      Dtm_graph_equation_2 _UU0393_ _UU03c4_1 _UU03c3_ t t0 hind hind0 ->
       f0 _UU0393_ _UU03c4_1 _UU03c3_ t t0 hind
         (f20 _UU0393_ (Definitions.Arrow _UU03c3_ _UU03c4_1) t
           (coq_Dtm _UU0393_ (Definitions.Arrow _UU03c3_ _UU03c4_1) t) hind)
         hind0
         (f20 _UU0393_ _UU03c3_ t0 (coq_Dtm _UU0393_ _UU03c3_ t0) hind0);
      Dtm_graph_equation_3 _UU0393_ _UU03c4_2 _UU03c3_0 t1 hind ->
       f1 _UU0393_ _UU03c4_2 _UU03c3_0 t1 hind
         (f20 (Datatypes.Coq_cons _UU03c3_0 _UU0393_) _UU03c4_2 t1
           (coq_Dtm (Datatypes.Coq_cons _UU03c3_0 _UU0393_) _UU03c4_2 t1)
           hind);
      Dtm_graph_equation_4 _UU0393_ _UU03c4_3 n t2 ->
       f2 _UU0393_ _UU03c4_3 n t2;
      Dtm_graph_equation_5 _UU0393_ _UU03c4_4 n0 t3 t4 hind ->
       f3 _UU0393_ _UU03c4_4 n0 t3 t4 hind
         (f20 _UU0393_ (Definitions.Array n0 _UU03c4_4) t4
           (coq_Dtm _UU0393_ (Definitions.Array n0 _UU03c4_4) t4) hind);
      Dtm_graph_equation_6 _UU0393_ r -> f4 _UU0393_ r;
      Dtm_graph_refinement_7 _UU0393_ t5 t6 hind hind0 ->
       f5 _UU0393_ t5 t6 hind
         (f20 _UU0393_ Definitions.Real t5
           (coq_Dtm _UU0393_ Definitions.Real t5) hind) hind0
         (f21 _UU0393_ t5 (coq_Dtm _UU0393_ Definitions.Real t5) t6
           (let {refine = coq_Dtm _UU0393_ Definitions.Real t5} in
            let {refine0 = coq_Dtm _UU0393_ Definitions.Real t6} in
            Definitions.Coq_tuple Definitions.Real Definitions.Real
            (Definitions.Coq_add (Definitions.Coq_first Definitions.Real
            Definitions.Real refine) (Definitions.Coq_first Definitions.Real
            Definitions.Real refine0)) (Definitions.Coq_add
            (Definitions.Coq_second Definitions.Real Definitions.Real refine)
            (Definitions.Coq_second Definitions.Real Definitions.Real
            refine0))) hind0);
      Dtm_graph_refinement_8 _UU0393_ t7 t8 hind hind0 ->
       f6 _UU0393_ t7 t8 hind
         (f20 _UU0393_ Definitions.Real t7
           (coq_Dtm _UU0393_ Definitions.Real t7) hind) hind0
         (f23 _UU0393_ t7 (coq_Dtm _UU0393_ Definitions.Real t7) t8
           (let {refine = coq_Dtm _UU0393_ Definitions.Real t7} in
            let {refine0 = coq_Dtm _UU0393_ Definitions.Real t8} in
            Definitions.Coq_tuple Definitions.Real Definitions.Real
            (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
            Definitions.Real refine) (Definitions.Coq_first Definitions.Real
            Definitions.Real refine0)) (Definitions.Coq_add
            (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
            Definitions.Real refine) (Definitions.Coq_second Definitions.Real
            Definitions.Real refine0)) (Definitions.Coq_mul
            (Definitions.Coq_first Definitions.Real Definitions.Real refine0)
            (Definitions.Coq_second Definitions.Real Definitions.Real
            refine)))) hind0);
      Dtm_graph_equation_9 _UU0393_ t9 hind ->
       f7 _UU0393_ t9 hind
         (f20 _UU0393_ Definitions.Nat t9
           (coq_Dtm _UU0393_ Definitions.Nat t9) hind);
      Dtm_graph_equation_10 _UU0393_ n1 -> f8 _UU0393_ n1;
      Dtm_graph_equation_11 _UU0393_ _UU03c4_5 t10 t11 t12 hind hind0
       hind1 ->
       f9 _UU0393_ _UU03c4_5 t10 t11 t12 hind
         (f20 _UU0393_ (Definitions.Arrow _UU03c4_5 _UU03c4_5) t10
           (coq_Dtm _UU0393_ (Definitions.Arrow _UU03c4_5 _UU03c4_5) t10)
           hind) hind0
         (f20 _UU0393_ Definitions.Nat t11
           (coq_Dtm _UU0393_ Definitions.Nat t11) hind0) hind1
         (f20 _UU0393_ _UU03c4_5 t12 (coq_Dtm _UU0393_ _UU03c4_5 t12) hind1);
      Dtm_graph_equation_12 _UU0393_ _UU03c4_6 _UU03c3_1 t13 t14 hind
       hind0 ->
       f10 _UU0393_ _UU03c4_6 _UU03c3_1 t13 t14 hind
         (f20 _UU0393_ _UU03c4_6 t13 (coq_Dtm _UU0393_ _UU03c4_6 t13) hind)
         hind0
         (f20 _UU0393_ _UU03c3_1 t14 (coq_Dtm _UU0393_ _UU03c3_1 t14) hind0);
      Dtm_graph_equation_13 _UU0393_ _UU03c4_7 _UU03c3_2 t15 hind ->
       f11 _UU0393_ _UU03c4_7 _UU03c3_2 t15 hind
         (f20 _UU0393_ (Definitions.Prod _UU03c4_7 _UU03c3_2) t15
           (coq_Dtm _UU0393_ (Definitions.Prod _UU03c4_7 _UU03c3_2) t15)
           hind);
      Dtm_graph_equation_14 _UU0393_ _UU03c3_3 _UU03c4_8 t16 hind ->
       f12 _UU0393_ _UU03c3_3 _UU03c4_8 t16 hind
         (f20 _UU0393_ (Definitions.Prod _UU03c4_8 _UU03c3_3) t16
           (coq_Dtm _UU0393_ (Definitions.Prod _UU03c4_8 _UU03c3_3) t16)
           hind);
      Dtm_graph_equation_15 _UU0393_ _UU03c1_ _UU03c4_9 _UU03c3_4 t17 t18 t19
       hind hind0 hind1 ->
       f13 _UU0393_ _UU03c1_ _UU03c4_9 _UU03c3_4 t17 t18 t19 hind
         (f20 _UU0393_ (Definitions.Sum _UU03c4_9 _UU03c3_4) t17
           (coq_Dtm _UU0393_ (Definitions.Sum _UU03c4_9 _UU03c3_4) t17) hind)
         hind0
         (f20 _UU0393_ (Definitions.Arrow _UU03c4_9 _UU03c1_) t18
           (coq_Dtm _UU0393_ (Definitions.Arrow _UU03c4_9 _UU03c1_) t18)
           hind0) hind1
         (f20 _UU0393_ (Definitions.Arrow _UU03c3_4 _UU03c1_) t19
           (coq_Dtm _UU0393_ (Definitions.Arrow _UU03c3_4 _UU03c1_) t19)
           hind1);
      Dtm_graph_equation_16 _UU0393_ _UU03c4_10 _UU03c3_5 t20 hind ->
       f14 _UU0393_ _UU03c4_10 _UU03c3_5 t20 hind
         (f20 _UU0393_ _UU03c4_10 t20 (coq_Dtm _UU0393_ _UU03c4_10 t20) hind);
      Dtm_graph_equation_17 _UU0393_ _UU03c4_11 _UU03c3_6 t21 hind ->
       f15 _UU0393_ _UU03c4_11 _UU03c3_6 t21 hind
         (f20 _UU0393_ _UU03c3_6 t21 (coq_Dtm _UU0393_ _UU03c3_6 t21) hind)};
   f21 _ _ _ _ _ d =
     case d of {
      Dtm_clause_10_graph_refinement_1 _UU0393_ t5 refine t6 hind hind0 ->
       f16 _UU0393_ t5 refine t6 hind
         (f20 _UU0393_ Definitions.Real t6
           (coq_Dtm _UU0393_ Definitions.Real t6) hind) hind0
         (f22 _UU0393_ t6 (coq_Dtm _UU0393_ Definitions.Real t6) t5 refine
           (let {refine0 = coq_Dtm _UU0393_ Definitions.Real t6} in
            Definitions.Coq_tuple Definitions.Real Definitions.Real
            (Definitions.Coq_add (Definitions.Coq_first Definitions.Real
            Definitions.Real refine) (Definitions.Coq_first Definitions.Real
            Definitions.Real refine0)) (Definitions.Coq_add
            (Definitions.Coq_second Definitions.Real Definitions.Real refine)
            (Definitions.Coq_second Definitions.Real Definitions.Real
            refine0))) hind0)};
   f22 _ _ _ _ _ _ d =
     case d of {
      Dtm_clause_10_clause_1_graph_equation_1 _UU0393_ t6 refine0 t5
       refine -> f17 _UU0393_ t6 refine0 t5 refine};
   f23 _ _ _ _ _ d =
     case d of {
      Dtm_clause_11_graph_refinement_1 _UU0393_ t7 refine t8 hind hind0 ->
       f18 _UU0393_ t7 refine t8 hind
         (f20 _UU0393_ Definitions.Real t8
           (coq_Dtm _UU0393_ Definitions.Real t8) hind) hind0
         (f24 _UU0393_ t8 (coq_Dtm _UU0393_ Definitions.Real t8) t7 refine
           (let {refine0 = coq_Dtm _UU0393_ Definitions.Real t8} in
            Definitions.Coq_tuple Definitions.Real Definitions.Real
            (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
            Definitions.Real refine) (Definitions.Coq_first Definitions.Real
            Definitions.Real refine0)) (Definitions.Coq_add
            (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
            Definitions.Real refine) (Definitions.Coq_second Definitions.Real
            Definitions.Real refine0)) (Definitions.Coq_mul
            (Definitions.Coq_first Definitions.Real Definitions.Real refine0)
            (Definitions.Coq_second Definitions.Real Definitions.Real
            refine)))) hind0)};
   f24 _ _ _ _ _ _ d =
     case d of {
      Dtm_clause_11_clause_1_graph_equation_1 _UU0393_ t8 refine0 t7
       refine -> f19 _UU0393_ t8 refine0 t7 refine}}
  in f20

coq_Dtm_graph_rect :: ((Definitions.Ctx Definitions.Coq_ty) ->
                      Definitions.Coq_ty -> (Definitions.Var
                      Definitions.Coq_ty) -> a1) -> ((Definitions.Ctx
                      Definitions.Coq_ty) -> Definitions.Coq_ty ->
                      Definitions.Coq_ty -> Definitions.Coq_tm ->
                      Definitions.Coq_tm -> Dtm_graph -> a1 -> Dtm_graph ->
                      a1 -> a1) -> ((Definitions.Ctx Definitions.Coq_ty) ->
                      Definitions.Coq_ty -> Definitions.Coq_ty ->
                      Definitions.Coq_tm -> Dtm_graph -> a1 -> a1) ->
                      ((Definitions.Ctx Definitions.Coq_ty) ->
                      Definitions.Coq_ty -> Datatypes.Coq_nat -> (Fin.Coq_t
                      -> Definitions.Coq_tm) -> a1) -> ((Definitions.Ctx
                      Definitions.Coq_ty) -> Definitions.Coq_ty ->
                      Datatypes.Coq_nat -> Fin.Coq_t -> Definitions.Coq_tm ->
                      Dtm_graph -> a1 -> a1) -> ((Definitions.Ctx
                      Definitions.Coq_ty) -> Rdefinitions.RbaseSymbolsImpl__R
                      -> a1) -> ((Definitions.Ctx Definitions.Coq_ty) ->
                      Definitions.Coq_tm -> Definitions.Coq_tm -> Dtm_graph
                      -> a1 -> Dtm_clause_10_graph -> a2 -> a1) ->
                      ((Definitions.Ctx Definitions.Coq_ty) ->
                      Definitions.Coq_tm -> Definitions.Coq_tm -> Dtm_graph
                      -> a1 -> Dtm_clause_11_graph -> a4 -> a1) ->
                      ((Definitions.Ctx Definitions.Coq_ty) ->
                      Definitions.Coq_tm -> Dtm_graph -> a1 -> a1) ->
                      ((Definitions.Ctx Definitions.Coq_ty) ->
                      Datatypes.Coq_nat -> a1) -> ((Definitions.Ctx
                      Definitions.Coq_ty) -> Definitions.Coq_ty ->
                      Definitions.Coq_tm -> Definitions.Coq_tm ->
                      Definitions.Coq_tm -> Dtm_graph -> a1 -> Dtm_graph ->
                      a1 -> Dtm_graph -> a1 -> a1) -> ((Definitions.Ctx
                      Definitions.Coq_ty) -> Definitions.Coq_ty ->
                      Definitions.Coq_ty -> Definitions.Coq_tm ->
                      Definitions.Coq_tm -> Dtm_graph -> a1 -> Dtm_graph ->
                      a1 -> a1) -> ((Definitions.Ctx Definitions.Coq_ty) ->
                      Definitions.Coq_ty -> Definitions.Coq_ty ->
                      Definitions.Coq_tm -> Dtm_graph -> a1 -> a1) ->
                      ((Definitions.Ctx Definitions.Coq_ty) ->
                      Definitions.Coq_ty -> Definitions.Coq_ty ->
                      Definitions.Coq_tm -> Dtm_graph -> a1 -> a1) ->
                      ((Definitions.Ctx Definitions.Coq_ty) ->
                      Definitions.Coq_ty -> Definitions.Coq_ty ->
                      Definitions.Coq_ty -> Definitions.Coq_tm ->
                      Definitions.Coq_tm -> Definitions.Coq_tm -> Dtm_graph
                      -> a1 -> Dtm_graph -> a1 -> Dtm_graph -> a1 -> a1) ->
                      ((Definitions.Ctx Definitions.Coq_ty) ->
                      Definitions.Coq_ty -> Definitions.Coq_ty ->
                      Definitions.Coq_tm -> Dtm_graph -> a1 -> a1) ->
                      ((Definitions.Ctx Definitions.Coq_ty) ->
                      Definitions.Coq_ty -> Definitions.Coq_ty ->
                      Definitions.Coq_tm -> Dtm_graph -> a1 -> a1) ->
                      ((Definitions.Ctx Definitions.Coq_ty) ->
                      Definitions.Coq_tm -> Definitions.Coq_tm ->
                      Definitions.Coq_tm -> Dtm_graph -> a1 ->
                      Dtm_clause_10_clause_1_graph -> a3 -> a2) ->
                      ((Definitions.Ctx Definitions.Coq_ty) ->
                      Definitions.Coq_tm -> Definitions.Coq_tm ->
                      Definitions.Coq_tm -> Definitions.Coq_tm -> a3) ->
                      ((Definitions.Ctx Definitions.Coq_ty) ->
                      Definitions.Coq_tm -> Definitions.Coq_tm ->
                      Definitions.Coq_tm -> Dtm_graph -> a1 ->
                      Dtm_clause_11_clause_1_graph -> a5 -> a4) ->
                      ((Definitions.Ctx Definitions.Coq_ty) ->
                      Definitions.Coq_tm -> Definitions.Coq_tm ->
                      Definitions.Coq_tm -> Definitions.Coq_tm -> a5) ->
                      (Definitions.Ctx Definitions.Coq_ty) ->
                      Definitions.Coq_ty -> Definitions.Coq_tm ->
                      Definitions.Coq_tm -> Dtm_graph -> a1
coq_Dtm_graph_rect =
  coq_Dtm_graph_mut

coq_Dtm_graph_correct :: (Definitions.Ctx Definitions.Coq_ty) ->
                         Definitions.Coq_ty -> Definitions.Coq_tm ->
                         Dtm_graph
coq_Dtm_graph_correct _UU0393_ _ t =
  case t of {
   Definitions.Coq_var _UU03c4_ v ->
    Logic.eq_rect_r (Definitions.Coq_var (coq_Dt _UU03c4_)
      (coq_Dv _UU0393_ _UU03c4_ v)) (Dtm_graph_equation_1 _UU0393_ _UU03c4_
      v) (coq_Dtm _UU0393_ _UU03c4_ (Definitions.Coq_var _UU03c4_ v));
   Definitions.Coq_app _UU03c4_ _UU03c3_ t1 t2 ->
    Logic.eq_rect_r (Definitions.Coq_app
      (let {
        dt _UU03c4_0 =
          case _UU03c4_0 of {
           Definitions.Real -> Definitions.Prod Definitions.Real
            Definitions.Real;
           Definitions.Nat -> Definitions.Nat;
           Definitions.Array n t0 -> Definitions.Array n (dt t0);
           Definitions.Arrow t3 t4 -> Definitions.Arrow (dt t3) (dt t4);
           Definitions.Prod t3 t4 -> Definitions.Prod (dt t3) (dt t4);
           Definitions.Sum t3 t4 -> Definitions.Sum (dt t3) (dt t4)}}
       in dt _UU03c4_)
      (let {
        dt _UU03c4_0 =
          case _UU03c4_0 of {
           Definitions.Real -> Definitions.Prod Definitions.Real
            Definitions.Real;
           Definitions.Nat -> Definitions.Nat;
           Definitions.Array n t0 -> Definitions.Array n (dt t0);
           Definitions.Arrow t3 t4 -> Definitions.Arrow (dt t3) (dt t4);
           Definitions.Prod t3 t4 -> Definitions.Prod (dt t3) (dt t4);
           Definitions.Sum t3 t4 -> Definitions.Sum (dt t3) (dt t4)}}
       in dt _UU03c3_)
      (coq_Dtm _UU0393_ (Definitions.Arrow _UU03c3_ _UU03c4_) t1)
      (coq_Dtm _UU0393_ _UU03c3_ t2)) (Dtm_graph_equation_2 _UU0393_ _UU03c4_
      _UU03c3_ t1 t2
      (coq_Dtm_graph_correct _UU0393_ (Definitions.Arrow _UU03c3_ _UU03c4_)
        t1) (coq_Dtm_graph_correct _UU0393_ _UU03c3_ t2))
      (coq_Dtm _UU0393_ _UU03c4_ (Definitions.Coq_app _UU03c4_ _UU03c3_ t1
        t2));
   Definitions.Coq_abs _UU03c4_ _UU03c3_ t0 ->
    Logic.eq_rect_r (Definitions.Coq_abs (coq_Dt _UU03c4_) (coq_Dt _UU03c3_)
      (coq_Dtm (Datatypes.Coq_cons _UU03c3_ _UU0393_) _UU03c4_ t0))
      (Dtm_graph_equation_3 _UU0393_ _UU03c4_ _UU03c3_ t0
      (coq_Dtm_graph_correct (Datatypes.Coq_cons _UU03c3_ _UU0393_) _UU03c4_
        t0))
      (coq_Dtm _UU0393_ (Definitions.Arrow _UU03c3_ _UU03c4_)
        (Definitions.Coq_abs _UU03c4_ _UU03c3_ t0));
   Definitions.Coq_build _UU03c4_ n t0 ->
    Logic.eq_rect_r (Definitions.Coq_build (coq_Dt _UU03c4_) n
      (Basics.compose (coq_Dtm _UU0393_ _UU03c4_) t0)) (Dtm_graph_equation_4
      _UU0393_ _UU03c4_ n t0)
      (coq_Dtm _UU0393_ (Definitions.Array n _UU03c4_) (Definitions.Coq_build
        _UU03c4_ n t0));
   Definitions.Coq_get _UU03c4_ n t0 t1 ->
    Logic.eq_rect_r (Definitions.Coq_get
      (let {
        dt _UU03c4_0 =
          case _UU03c4_0 of {
           Definitions.Real -> Definitions.Prod Definitions.Real
            Definitions.Real;
           Definitions.Nat -> Definitions.Nat;
           Definitions.Array n0 t2 -> Definitions.Array n0 (dt t2);
           Definitions.Arrow t2 t3 -> Definitions.Arrow (dt t2) (dt t3);
           Definitions.Prod t2 t3 -> Definitions.Prod (dt t2) (dt t3);
           Definitions.Sum t2 t3 -> Definitions.Sum (dt t2) (dt t3)}}
       in dt _UU03c4_) n t0
      (coq_Dtm _UU0393_ (Definitions.Array n _UU03c4_) t1))
      (Dtm_graph_equation_5 _UU0393_ _UU03c4_ n t0 t1
      (coq_Dtm_graph_correct _UU0393_ (Definitions.Array n _UU03c4_) t1))
      (coq_Dtm _UU0393_ _UU03c4_ (Definitions.Coq_get _UU03c4_ n t0 t1));
   Definitions.Coq_rval r ->
    Logic.eq_rect_r (Definitions.Coq_tuple Definitions.Real Definitions.Real
      (Definitions.Coq_rval r) (Definitions.Coq_rval
      (Rdefinitions.coq_IZR BinNums.Z0))) (Dtm_graph_equation_6 _UU0393_ r)
      (coq_Dtm _UU0393_ Definitions.Real (Definitions.Coq_rval r));
   Definitions.Coq_add t1 t2 ->
    Logic.eq_rect_r
      (let {refine = coq_Dtm _UU0393_ Definitions.Real t1} in
       let {refine0 = coq_Dtm _UU0393_ Definitions.Real t2} in
       Definitions.Coq_tuple Definitions.Real Definitions.Real
       (Definitions.Coq_add (Definitions.Coq_first Definitions.Real
       Definitions.Real refine) (Definitions.Coq_first Definitions.Real
       Definitions.Real refine0)) (Definitions.Coq_add
       (Definitions.Coq_second Definitions.Real Definitions.Real refine)
       (Definitions.Coq_second Definitions.Real Definitions.Real refine0)))
      (Dtm_graph_refinement_7 _UU0393_ t1 t2
      (coq_Dtm_graph_correct _UU0393_ Definitions.Real t1)
      (let {refine = coq_Dtm _UU0393_ Definitions.Real t1} in
       Logic.eq_rect_r
         (let {refine0 = coq_Dtm _UU0393_ Definitions.Real t2} in
          Definitions.Coq_tuple Definitions.Real Definitions.Real
          (Definitions.Coq_add (Definitions.Coq_first Definitions.Real
          Definitions.Real refine) (Definitions.Coq_first Definitions.Real
          Definitions.Real refine0)) (Definitions.Coq_add
          (Definitions.Coq_second Definitions.Real Definitions.Real refine)
          (Definitions.Coq_second Definitions.Real Definitions.Real refine0)))
         (Dtm_clause_10_graph_refinement_1 _UU0393_ t1 refine t2
         (coq_Dtm_graph_correct _UU0393_ Definitions.Real t2)
         (let {refine0 = coq_Dtm _UU0393_ Definitions.Real t2} in
          Logic.eq_rect_r (Definitions.Coq_tuple Definitions.Real
            Definitions.Real (Definitions.Coq_add (Definitions.Coq_first
            Definitions.Real Definitions.Real refine) (Definitions.Coq_first
            Definitions.Real Definitions.Real refine0)) (Definitions.Coq_add
            (Definitions.Coq_second Definitions.Real Definitions.Real refine)
            (Definitions.Coq_second Definitions.Real Definitions.Real
            refine0))) (Dtm_clause_10_clause_1_graph_equation_1 _UU0393_ t2
            refine0 t1 refine) (Definitions.Coq_tuple Definitions.Real
            Definitions.Real (Definitions.Coq_add (Definitions.Coq_first
            Definitions.Real Definitions.Real refine) (Definitions.Coq_first
            Definitions.Real Definitions.Real refine0)) (Definitions.Coq_add
            (Definitions.Coq_second Definitions.Real Definitions.Real refine)
            (Definitions.Coq_second Definitions.Real Definitions.Real
            refine0)))))
         (let {refine0 = coq_Dtm _UU0393_ Definitions.Real t2} in
          Definitions.Coq_tuple Definitions.Real Definitions.Real
          (Definitions.Coq_add (Definitions.Coq_first Definitions.Real
          Definitions.Real refine) (Definitions.Coq_first Definitions.Real
          Definitions.Real refine0)) (Definitions.Coq_add
          (Definitions.Coq_second Definitions.Real Definitions.Real refine)
          (Definitions.Coq_second Definitions.Real Definitions.Real refine0)))))
      (coq_Dtm _UU0393_ Definitions.Real (Definitions.Coq_add t1 t2));
   Definitions.Coq_mul t1 t2 ->
    Logic.eq_rect_r
      (let {refine = coq_Dtm _UU0393_ Definitions.Real t1} in
       let {refine0 = coq_Dtm _UU0393_ Definitions.Real t2} in
       Definitions.Coq_tuple Definitions.Real Definitions.Real
       (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
       Definitions.Real refine) (Definitions.Coq_first Definitions.Real
       Definitions.Real refine0)) (Definitions.Coq_add (Definitions.Coq_mul
       (Definitions.Coq_first Definitions.Real Definitions.Real refine)
       (Definitions.Coq_second Definitions.Real Definitions.Real refine0))
       (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
       Definitions.Real refine0) (Definitions.Coq_second Definitions.Real
       Definitions.Real refine)))) (Dtm_graph_refinement_8 _UU0393_ t1 t2
      (coq_Dtm_graph_correct _UU0393_ Definitions.Real t1)
      (let {refine = coq_Dtm _UU0393_ Definitions.Real t1} in
       Logic.eq_rect_r
         (let {refine0 = coq_Dtm _UU0393_ Definitions.Real t2} in
          Definitions.Coq_tuple Definitions.Real Definitions.Real
          (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
          Definitions.Real refine) (Definitions.Coq_first Definitions.Real
          Definitions.Real refine0)) (Definitions.Coq_add
          (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
          Definitions.Real refine) (Definitions.Coq_second Definitions.Real
          Definitions.Real refine0)) (Definitions.Coq_mul
          (Definitions.Coq_first Definitions.Real Definitions.Real refine0)
          (Definitions.Coq_second Definitions.Real Definitions.Real refine))))
         (Dtm_clause_11_graph_refinement_1 _UU0393_ t1 refine t2
         (coq_Dtm_graph_correct _UU0393_ Definitions.Real t2)
         (let {refine0 = coq_Dtm _UU0393_ Definitions.Real t2} in
          Logic.eq_rect_r (Definitions.Coq_tuple Definitions.Real
            Definitions.Real (Definitions.Coq_mul (Definitions.Coq_first
            Definitions.Real Definitions.Real refine) (Definitions.Coq_first
            Definitions.Real Definitions.Real refine0)) (Definitions.Coq_add
            (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
            Definitions.Real refine) (Definitions.Coq_second Definitions.Real
            Definitions.Real refine0)) (Definitions.Coq_mul
            (Definitions.Coq_first Definitions.Real Definitions.Real refine0)
            (Definitions.Coq_second Definitions.Real Definitions.Real
            refine)))) (Dtm_clause_11_clause_1_graph_equation_1 _UU0393_ t2
            refine0 t1 refine) (Definitions.Coq_tuple Definitions.Real
            Definitions.Real (Definitions.Coq_mul (Definitions.Coq_first
            Definitions.Real Definitions.Real refine) (Definitions.Coq_first
            Definitions.Real Definitions.Real refine0)) (Definitions.Coq_add
            (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
            Definitions.Real refine) (Definitions.Coq_second Definitions.Real
            Definitions.Real refine0)) (Definitions.Coq_mul
            (Definitions.Coq_first Definitions.Real Definitions.Real refine0)
            (Definitions.Coq_second Definitions.Real Definitions.Real
            refine))))))
         (let {refine0 = coq_Dtm _UU0393_ Definitions.Real t2} in
          Definitions.Coq_tuple Definitions.Real Definitions.Real
          (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
          Definitions.Real refine) (Definitions.Coq_first Definitions.Real
          Definitions.Real refine0)) (Definitions.Coq_add
          (Definitions.Coq_mul (Definitions.Coq_first Definitions.Real
          Definitions.Real refine) (Definitions.Coq_second Definitions.Real
          Definitions.Real refine0)) (Definitions.Coq_mul
          (Definitions.Coq_first Definitions.Real Definitions.Real refine0)
          (Definitions.Coq_second Definitions.Real Definitions.Real refine))))))
      (coq_Dtm _UU0393_ Definitions.Real (Definitions.Coq_mul t1 t2));
   Definitions.Coq_nsucc t0 ->
    Logic.eq_rect_r (Definitions.Coq_nsucc
      (coq_Dtm _UU0393_ Definitions.Nat t0)) (Dtm_graph_equation_9 _UU0393_
      t0 (coq_Dtm_graph_correct _UU0393_ Definitions.Nat t0))
      (coq_Dtm _UU0393_ Definitions.Nat (Definitions.Coq_nsucc t0));
   Definitions.Coq_nval n ->
    Logic.eq_rect_r (Definitions.Coq_nval n) (Dtm_graph_equation_10 _UU0393_
      n) (coq_Dtm _UU0393_ Definitions.Nat (Definitions.Coq_nval n));
   Definitions.Coq_nrec _UU03c4_ t1 t2 t3 ->
    Logic.eq_rect_r (Definitions.Coq_nrec
      (let {
        dt _UU03c4_0 =
          case _UU03c4_0 of {
           Definitions.Real -> Definitions.Prod Definitions.Real
            Definitions.Real;
           Definitions.Nat -> Definitions.Nat;
           Definitions.Array n t0 -> Definitions.Array n (dt t0);
           Definitions.Arrow t4 t5 -> Definitions.Arrow (dt t4) (dt t5);
           Definitions.Prod t4 t5 -> Definitions.Prod (dt t4) (dt t5);
           Definitions.Sum t4 t5 -> Definitions.Sum (dt t4) (dt t5)}}
       in dt _UU03c4_)
      (coq_Dtm _UU0393_ (Definitions.Arrow _UU03c4_ _UU03c4_) t1)
      (coq_Dtm _UU0393_ Definitions.Nat t2) (coq_Dtm _UU0393_ _UU03c4_ t3))
      (Dtm_graph_equation_11 _UU0393_ _UU03c4_ t1 t2 t3
      (coq_Dtm_graph_correct _UU0393_ (Definitions.Arrow _UU03c4_ _UU03c4_)
        t1) (coq_Dtm_graph_correct _UU0393_ Definitions.Nat t2)
      (coq_Dtm_graph_correct _UU0393_ _UU03c4_ t3))
      (coq_Dtm _UU0393_ _UU03c4_ (Definitions.Coq_nrec _UU03c4_ t1 t2 t3));
   Definitions.Coq_tuple _UU03c4_ _UU03c3_ t1 t2 ->
    Logic.eq_rect_r (Definitions.Coq_tuple (coq_Dt _UU03c4_)
      (coq_Dt _UU03c3_) (coq_Dtm _UU0393_ _UU03c4_ t1)
      (coq_Dtm _UU0393_ _UU03c3_ t2)) (Dtm_graph_equation_12 _UU0393_
      _UU03c4_ _UU03c3_ t1 t2 (coq_Dtm_graph_correct _UU0393_ _UU03c4_ t1)
      (coq_Dtm_graph_correct _UU0393_ _UU03c3_ t2))
      (coq_Dtm _UU0393_ (Definitions.Prod _UU03c4_ _UU03c3_)
        (Definitions.Coq_tuple _UU03c4_ _UU03c3_ t1 t2));
   Definitions.Coq_first _UU03c4_ _UU03c3_ t0 ->
    Logic.eq_rect_r (Definitions.Coq_first
      (let {
        dt _UU03c4_0 =
          case _UU03c4_0 of {
           Definitions.Real -> Definitions.Prod Definitions.Real
            Definitions.Real;
           Definitions.Nat -> Definitions.Nat;
           Definitions.Array n t1 -> Definitions.Array n (dt t1);
           Definitions.Arrow t1 t2 -> Definitions.Arrow (dt t1) (dt t2);
           Definitions.Prod t1 t2 -> Definitions.Prod (dt t1) (dt t2);
           Definitions.Sum t1 t2 -> Definitions.Sum (dt t1) (dt t2)}}
       in dt _UU03c4_)
      (let {
        dt _UU03c4_0 =
          case _UU03c4_0 of {
           Definitions.Real -> Definitions.Prod Definitions.Real
            Definitions.Real;
           Definitions.Nat -> Definitions.Nat;
           Definitions.Array n t1 -> Definitions.Array n (dt t1);
           Definitions.Arrow t1 t2 -> Definitions.Arrow (dt t1) (dt t2);
           Definitions.Prod t1 t2 -> Definitions.Prod (dt t1) (dt t2);
           Definitions.Sum t1 t2 -> Definitions.Sum (dt t1) (dt t2)}}
       in dt _UU03c3_)
      (coq_Dtm _UU0393_ (Definitions.Prod _UU03c4_ _UU03c3_) t0))
      (Dtm_graph_equation_13 _UU0393_ _UU03c4_ _UU03c3_ t0
      (coq_Dtm_graph_correct _UU0393_ (Definitions.Prod _UU03c4_ _UU03c3_)
        t0))
      (coq_Dtm _UU0393_ _UU03c4_ (Definitions.Coq_first _UU03c4_ _UU03c3_
        t0));
   Definitions.Coq_second _UU03c4_ _UU03c3_ t0 ->
    Logic.eq_rect_r (Definitions.Coq_second
      (let {
        dt _UU03c4_0 =
          case _UU03c4_0 of {
           Definitions.Real -> Definitions.Prod Definitions.Real
            Definitions.Real;
           Definitions.Nat -> Definitions.Nat;
           Definitions.Array n t1 -> Definitions.Array n (dt t1);
           Definitions.Arrow t1 t2 -> Definitions.Arrow (dt t1) (dt t2);
           Definitions.Prod t1 t2 -> Definitions.Prod (dt t1) (dt t2);
           Definitions.Sum t1 t2 -> Definitions.Sum (dt t1) (dt t2)}}
       in dt _UU03c4_)
      (let {
        dt _UU03c4_0 =
          case _UU03c4_0 of {
           Definitions.Real -> Definitions.Prod Definitions.Real
            Definitions.Real;
           Definitions.Nat -> Definitions.Nat;
           Definitions.Array n t1 -> Definitions.Array n (dt t1);
           Definitions.Arrow t1 t2 -> Definitions.Arrow (dt t1) (dt t2);
           Definitions.Prod t1 t2 -> Definitions.Prod (dt t1) (dt t2);
           Definitions.Sum t1 t2 -> Definitions.Sum (dt t1) (dt t2)}}
       in dt _UU03c3_)
      (coq_Dtm _UU0393_ (Definitions.Prod _UU03c4_ _UU03c3_) t0))
      (Dtm_graph_equation_14 _UU0393_ _UU03c3_ _UU03c4_ t0
      (coq_Dtm_graph_correct _UU0393_ (Definitions.Prod _UU03c4_ _UU03c3_)
        t0))
      (coq_Dtm _UU0393_ _UU03c3_ (Definitions.Coq_second _UU03c4_ _UU03c3_
        t0));
   Definitions.Coq_case _UU03c4_ _UU03c3_ _UU03c1_ t1 t2 t3 ->
    Logic.eq_rect_r (Definitions.Coq_case
      (let {
        dt _UU03c4_0 =
          case _UU03c4_0 of {
           Definitions.Real -> Definitions.Prod Definitions.Real
            Definitions.Real;
           Definitions.Nat -> Definitions.Nat;
           Definitions.Array n t0 -> Definitions.Array n (dt t0);
           Definitions.Arrow t4 t5 -> Definitions.Arrow (dt t4) (dt t5);
           Definitions.Prod t4 t5 -> Definitions.Prod (dt t4) (dt t5);
           Definitions.Sum t4 t5 -> Definitions.Sum (dt t4) (dt t5)}}
       in dt _UU03c4_)
      (let {
        dt _UU03c4_0 =
          case _UU03c4_0 of {
           Definitions.Real -> Definitions.Prod Definitions.Real
            Definitions.Real;
           Definitions.Nat -> Definitions.Nat;
           Definitions.Array n t0 -> Definitions.Array n (dt t0);
           Definitions.Arrow t4 t5 -> Definitions.Arrow (dt t4) (dt t5);
           Definitions.Prod t4 t5 -> Definitions.Prod (dt t4) (dt t5);
           Definitions.Sum t4 t5 -> Definitions.Sum (dt t4) (dt t5)}}
       in dt _UU03c3_)
      (let {
        dt _UU03c4_0 =
          case _UU03c4_0 of {
           Definitions.Real -> Definitions.Prod Definitions.Real
            Definitions.Real;
           Definitions.Nat -> Definitions.Nat;
           Definitions.Array n t0 -> Definitions.Array n (dt t0);
           Definitions.Arrow t4 t5 -> Definitions.Arrow (dt t4) (dt t5);
           Definitions.Prod t4 t5 -> Definitions.Prod (dt t4) (dt t5);
           Definitions.Sum t4 t5 -> Definitions.Sum (dt t4) (dt t5)}}
       in dt _UU03c1_)
      (coq_Dtm _UU0393_ (Definitions.Sum _UU03c4_ _UU03c3_) t1)
      (coq_Dtm _UU0393_ (Definitions.Arrow _UU03c4_ _UU03c1_) t2)
      (coq_Dtm _UU0393_ (Definitions.Arrow _UU03c3_ _UU03c1_) t3))
      (Dtm_graph_equation_15 _UU0393_ _UU03c1_ _UU03c4_ _UU03c3_ t1 t2 t3
      (coq_Dtm_graph_correct _UU0393_ (Definitions.Sum _UU03c4_ _UU03c3_) t1)
      (coq_Dtm_graph_correct _UU0393_ (Definitions.Arrow _UU03c4_ _UU03c1_)
        t2)
      (coq_Dtm_graph_correct _UU0393_ (Definitions.Arrow _UU03c3_ _UU03c1_)
        t3))
      (coq_Dtm _UU0393_ _UU03c1_ (Definitions.Coq_case _UU03c4_ _UU03c3_
        _UU03c1_ t1 t2 t3));
   Definitions.Coq_inl _UU03c4_ _UU03c3_ t0 ->
    Logic.eq_rect_r (Definitions.Coq_inl (coq_Dt _UU03c4_)
      (let {
        dt _UU03c4_0 =
          case _UU03c4_0 of {
           Definitions.Real -> Definitions.Prod Definitions.Real
            Definitions.Real;
           Definitions.Nat -> Definitions.Nat;
           Definitions.Array n t1 -> Definitions.Array n (dt t1);
           Definitions.Arrow t1 t2 -> Definitions.Arrow (dt t1) (dt t2);
           Definitions.Prod t1 t2 -> Definitions.Prod (dt t1) (dt t2);
           Definitions.Sum t1 t2 -> Definitions.Sum (dt t1) (dt t2)}}
       in dt _UU03c3_) (coq_Dtm _UU0393_ _UU03c4_ t0)) (Dtm_graph_equation_16
      _UU0393_ _UU03c4_ _UU03c3_ t0
      (coq_Dtm_graph_correct _UU0393_ _UU03c4_ t0))
      (coq_Dtm _UU0393_ (Definitions.Sum _UU03c4_ _UU03c3_)
        (Definitions.Coq_inl _UU03c4_ _UU03c3_ t0));
   Definitions.Coq_inr _UU03c4_ _UU03c3_ t0 ->
    Logic.eq_rect_r (Definitions.Coq_inr
      (let {
        dt _UU03c4_0 =
          case _UU03c4_0 of {
           Definitions.Real -> Definitions.Prod Definitions.Real
            Definitions.Real;
           Definitions.Nat -> Definitions.Nat;
           Definitions.Array n t1 -> Definitions.Array n (dt t1);
           Definitions.Arrow t1 t2 -> Definitions.Arrow (dt t1) (dt t2);
           Definitions.Prod t1 t2 -> Definitions.Prod (dt t1) (dt t2);
           Definitions.Sum t1 t2 -> Definitions.Sum (dt t1) (dt t2)}}
       in dt _UU03c4_) (coq_Dt _UU03c3_) (coq_Dtm _UU0393_ _UU03c3_ t0))
      (Dtm_graph_equation_17 _UU0393_ _UU03c4_ _UU03c3_ t0
      (coq_Dtm_graph_correct _UU0393_ _UU03c3_ t0))
      (coq_Dtm _UU0393_ (Definitions.Sum _UU03c4_ _UU03c3_)
        (Definitions.Coq_inr _UU03c4_ _UU03c3_ t0))}

coq_Dtm_elim :: ((Definitions.Ctx Definitions.Coq_ty) -> Definitions.Coq_ty
                -> (Definitions.Var Definitions.Coq_ty) -> a1) ->
                ((Definitions.Ctx Definitions.Coq_ty) -> Definitions.Coq_ty
                -> Definitions.Coq_ty -> Definitions.Coq_tm ->
                Definitions.Coq_tm -> a1 -> a1 -> a1) -> ((Definitions.Ctx
                Definitions.Coq_ty) -> Definitions.Coq_ty ->
                Definitions.Coq_ty -> Definitions.Coq_tm -> a1 -> a1) ->
                ((Definitions.Ctx Definitions.Coq_ty) -> Definitions.Coq_ty
                -> Datatypes.Coq_nat -> (Fin.Coq_t -> Definitions.Coq_tm) ->
                a1) -> ((Definitions.Ctx Definitions.Coq_ty) ->
                Definitions.Coq_ty -> Datatypes.Coq_nat -> Fin.Coq_t ->
                Definitions.Coq_tm -> a1 -> a1) -> ((Definitions.Ctx
                Definitions.Coq_ty) -> Rdefinitions.RbaseSymbolsImpl__R ->
                a1) -> ((Definitions.Ctx Definitions.Coq_ty) ->
                Definitions.Coq_tm -> a1 -> a1) -> ((Definitions.Ctx
                Definitions.Coq_ty) -> Datatypes.Coq_nat -> a1) ->
                ((Definitions.Ctx Definitions.Coq_ty) -> Definitions.Coq_ty
                -> Definitions.Coq_tm -> Definitions.Coq_tm ->
                Definitions.Coq_tm -> a1 -> a1 -> a1 -> a1) ->
                ((Definitions.Ctx Definitions.Coq_ty) -> Definitions.Coq_ty
                -> Definitions.Coq_ty -> Definitions.Coq_tm ->
                Definitions.Coq_tm -> a1 -> a1 -> a1) -> ((Definitions.Ctx
                Definitions.Coq_ty) -> Definitions.Coq_ty ->
                Definitions.Coq_ty -> Definitions.Coq_tm -> a1 -> a1) ->
                ((Definitions.Ctx Definitions.Coq_ty) -> Definitions.Coq_ty
                -> Definitions.Coq_ty -> Definitions.Coq_tm -> a1 -> a1) ->
                ((Definitions.Ctx Definitions.Coq_ty) -> Definitions.Coq_ty
                -> Definitions.Coq_ty -> Definitions.Coq_ty ->
                Definitions.Coq_tm -> Definitions.Coq_tm ->
                Definitions.Coq_tm -> a1 -> a1 -> a1 -> a1) ->
                ((Definitions.Ctx Definitions.Coq_ty) -> Definitions.Coq_ty
                -> Definitions.Coq_ty -> Definitions.Coq_tm -> a1 -> a1) ->
                ((Definitions.Ctx Definitions.Coq_ty) -> Definitions.Coq_ty
                -> Definitions.Coq_ty -> Definitions.Coq_tm -> a1 -> a1) ->
                ((Definitions.Ctx Definitions.Coq_ty) -> Definitions.Coq_tm
                -> Definitions.Coq_tm -> Definitions.Coq_tm ->
                Definitions.Coq_tm -> () -> a1 -> () -> a1 -> a1) ->
                ((Definitions.Ctx Definitions.Coq_ty) -> Definitions.Coq_tm
                -> Definitions.Coq_tm -> Definitions.Coq_tm ->
                Definitions.Coq_tm -> () -> a1 -> () -> a1 -> a1) ->
                (Definitions.Ctx Definitions.Coq_ty) -> Definitions.Coq_ty ->
                Definitions.Coq_tm -> a1
coq_Dtm_elim f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 _UU0393_ _UU03c4_ t =
  coq_Dtm_graph_rect f (\_UU0393_0 _UU03c4_1 _UU03c3_ t0 t1 _ x _ ->
    f0 _UU0393_0 _UU03c4_1 _UU03c3_ t0 t1 x)
    (\_UU0393_0 _UU03c4_2 _UU03c3_0 t1 _ ->
    f1 _UU0393_0 _UU03c4_2 _UU03c3_0 t1) f2
    (\_UU0393_0 _UU03c4_4 n0 t3 t4 _ -> f3 _UU0393_0 _UU03c4_4 n0 t3 t4) f4
    (\_ _ _ _ x _ x0 -> x0 __ x) (\_ _ _ _ x _ x0 -> x0 __ x)
    (\_UU0393_0 t9 _ -> f5 _UU0393_0 t9) f6
    (\_UU0393_0 _UU03c4_5 t10 t11 t12 _ x _ x0 _ ->
    f7 _UU0393_0 _UU03c4_5 t10 t11 t12 x x0)
    (\_UU0393_0 _UU03c4_6 _UU03c3_1 t13 t14 _ x _ ->
    f8 _UU0393_0 _UU03c4_6 _UU03c3_1 t13 t14 x)
    (\_UU0393_0 _UU03c4_7 _UU03c3_2 t15 _ ->
    f9 _UU0393_0 _UU03c4_7 _UU03c3_2 t15)
    (\_UU0393_0 _UU03c3_3 _UU03c4_8 t16 _ ->
    f10 _UU0393_0 _UU03c3_3 _UU03c4_8 t16)
    (\_UU0393_0 _UU03c1_ _UU03c4_9 _UU03c3_4 t17 t18 t19 _ x _ x0 _ ->
    f11 _UU0393_0 _UU03c1_ _UU03c4_9 _UU03c3_4 t17 t18 t19 x x0)
    (\_UU0393_0 _UU03c4_10 _UU03c3_5 t20 _ ->
    f12 _UU0393_0 _UU03c4_10 _UU03c3_5 t20)
    (\_UU0393_0 _UU03c4_11 _UU03c3_6 t21 _ ->
    f13 _UU0393_0 _UU03c4_11 _UU03c3_6 t21) (\_ _ _ _ _ x _ x0 -> x0 __ x)
    f14 (\_ _ _ _ _ x _ x0 -> x0 __ x) f15 _UU0393_ _UU03c4_ t
    (coq_Dtm _UU0393_ _UU03c4_ t) (coq_Dtm_graph_correct _UU0393_ _UU03c4_ t)

coq_FunctionalElimination_Dtm :: ((Definitions.Ctx Definitions.Coq_ty) ->
                                 Definitions.Coq_ty -> (Definitions.Var
                                 Definitions.Coq_ty) -> a1) ->
                                 ((Definitions.Ctx Definitions.Coq_ty) ->
                                 Definitions.Coq_ty -> Definitions.Coq_ty ->
                                 Definitions.Coq_tm -> Definitions.Coq_tm ->
                                 a1 -> a1 -> a1) -> ((Definitions.Ctx
                                 Definitions.Coq_ty) -> Definitions.Coq_ty ->
                                 Definitions.Coq_ty -> Definitions.Coq_tm ->
                                 a1 -> a1) -> ((Definitions.Ctx
                                 Definitions.Coq_ty) -> Definitions.Coq_ty ->
                                 Datatypes.Coq_nat -> (Fin.Coq_t ->
                                 Definitions.Coq_tm) -> a1) ->
                                 ((Definitions.Ctx Definitions.Coq_ty) ->
                                 Definitions.Coq_ty -> Datatypes.Coq_nat ->
                                 Fin.Coq_t -> Definitions.Coq_tm -> a1 -> a1)
                                 -> ((Definitions.Ctx Definitions.Coq_ty) ->
                                 Rdefinitions.RbaseSymbolsImpl__R -> a1) ->
                                 ((Definitions.Ctx Definitions.Coq_ty) ->
                                 Definitions.Coq_tm -> a1 -> a1) ->
                                 ((Definitions.Ctx Definitions.Coq_ty) ->
                                 Datatypes.Coq_nat -> a1) ->
                                 ((Definitions.Ctx Definitions.Coq_ty) ->
                                 Definitions.Coq_ty -> Definitions.Coq_tm ->
                                 Definitions.Coq_tm -> Definitions.Coq_tm ->
                                 a1 -> a1 -> a1 -> a1) -> ((Definitions.Ctx
                                 Definitions.Coq_ty) -> Definitions.Coq_ty ->
                                 Definitions.Coq_ty -> Definitions.Coq_tm ->
                                 Definitions.Coq_tm -> a1 -> a1 -> a1) ->
                                 ((Definitions.Ctx Definitions.Coq_ty) ->
                                 Definitions.Coq_ty -> Definitions.Coq_ty ->
                                 Definitions.Coq_tm -> a1 -> a1) ->
                                 ((Definitions.Ctx Definitions.Coq_ty) ->
                                 Definitions.Coq_ty -> Definitions.Coq_ty ->
                                 Definitions.Coq_tm -> a1 -> a1) ->
                                 ((Definitions.Ctx Definitions.Coq_ty) ->
                                 Definitions.Coq_ty -> Definitions.Coq_ty ->
                                 Definitions.Coq_ty -> Definitions.Coq_tm ->
                                 Definitions.Coq_tm -> Definitions.Coq_tm ->
                                 a1 -> a1 -> a1 -> a1) -> ((Definitions.Ctx
                                 Definitions.Coq_ty) -> Definitions.Coq_ty ->
                                 Definitions.Coq_ty -> Definitions.Coq_tm ->
                                 a1 -> a1) -> ((Definitions.Ctx
                                 Definitions.Coq_ty) -> Definitions.Coq_ty ->
                                 Definitions.Coq_ty -> Definitions.Coq_tm ->
                                 a1 -> a1) -> ((Definitions.Ctx
                                 Definitions.Coq_ty) -> Definitions.Coq_tm ->
                                 Definitions.Coq_tm -> Definitions.Coq_tm ->
                                 Definitions.Coq_tm -> () -> a1 -> () -> a1
                                 -> a1) -> ((Definitions.Ctx
                                 Definitions.Coq_ty) -> Definitions.Coq_tm ->
                                 Definitions.Coq_tm -> Definitions.Coq_tm ->
                                 Definitions.Coq_tm -> () -> a1 -> () -> a1
                                 -> a1) -> (Definitions.Ctx
                                 Definitions.Coq_ty) -> Definitions.Coq_ty ->
                                 Definitions.Coq_tm -> a1
coq_FunctionalElimination_Dtm =
  coq_Dtm_elim

coq_FunctionalInduction_Dtm :: Classes.FunctionalInduction
                               ((Definitions.Ctx Definitions.Coq_ty) ->
                               Definitions.Coq_ty -> Definitions.Coq_tm ->
                               Definitions.Coq_tm)
coq_FunctionalInduction_Dtm =
  unsafeCoerce coq_Dtm_graph_correct

type Dsub =
  Definitions.Coq_ty -> (Definitions.Var Definitions.Coq_ty) ->
  Definitions.Coq_tm

type Dren =
  Definitions.Coq_ty -> (Definitions.Var Definitions.Coq_ty) ->
  Definitions.Var Definitions.Coq_ty

coq_Dt_lift_var :: (Datatypes.Coq_list Definitions.Coq_ty) ->
                   Definitions.Coq_ty -> (Definitions.Var Definitions.Coq_ty)
                   -> Definitions.Var Definitions.Coq_ty
coq_Dt_lift_var _UU0393_ _UU03c4_ h =
  Definitions.coq_Var_rect (\_UU0393_0 _UU03c4_0 -> Definitions.Top
    (let {
      map0 l =
        case l of {
         Datatypes.Coq_nil -> Datatypes.Coq_nil;
         Datatypes.Coq_cons a t -> Datatypes.Coq_cons (coq_Dt a) (map0 t)}}
     in map0 _UU0393_0) (coq_Dt _UU03c4_0))
    (\_UU0393_0 _UU03c4_0 _UU03c3_ _ iHVar -> Definitions.Pop
    (let {
      map0 l =
        case l of {
         Datatypes.Coq_nil -> Datatypes.Coq_nil;
         Datatypes.Coq_cons a t -> Datatypes.Coq_cons (coq_Dt a) (map0 t)}}
     in map0 _UU0393_0) (coq_Dt _UU03c4_0) (coq_Dt _UU03c3_) iHVar) _UU0393_
    _UU03c4_ h

