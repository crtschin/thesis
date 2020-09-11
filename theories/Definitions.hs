{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Definitions where

import qualified Prelude
import qualified Basics
import qualified BinNums
import qualified Classes
import qualified Datatypes
import qualified Fin
import qualified Init0
import qualified Logic
import qualified Logic0
import qualified Rdefinitions
import qualified Signature

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

data Coq_ty =
   Real
 | Nat
 | Array Datatypes.Coq_nat Coq_ty
 | Arrow Coq_ty Coq_ty
 | Prod Coq_ty Coq_ty
 | Sum Coq_ty Coq_ty

ty_rect :: a1 -> a1 -> (Datatypes.Coq_nat -> Coq_ty -> a1 -> a1) -> (Coq_ty
           -> a1 -> Coq_ty -> a1 -> a1) -> (Coq_ty -> a1 -> Coq_ty -> a1 ->
           a1) -> (Coq_ty -> a1 -> Coq_ty -> a1 -> a1) -> Coq_ty -> a1
ty_rect f f0 f1 f2 f3 f4 t =
  case t of {
   Real -> f;
   Nat -> f0;
   Array n t0 -> f1 n t0 (ty_rect f f0 f1 f2 f3 f4 t0);
   Arrow t0 t1 ->
    f2 t0 (ty_rect f f0 f1 f2 f3 f4 t0) t1 (ty_rect f f0 f1 f2 f3 f4 t1);
   Prod t0 t1 ->
    f3 t0 (ty_rect f f0 f1 f2 f3 f4 t0) t1 (ty_rect f f0 f1 f2 f3 f4 t1);
   Sum t0 t1 ->
    f4 t0 (ty_rect f f0 f1 f2 f3 f4 t0) t1 (ty_rect f f0 f1 f2 f3 f4 t1)}

ty_rec :: a1 -> a1 -> (Datatypes.Coq_nat -> Coq_ty -> a1 -> a1) -> (Coq_ty ->
          a1 -> Coq_ty -> a1 -> a1) -> (Coq_ty -> a1 -> Coq_ty -> a1 -> a1)
          -> (Coq_ty -> a1 -> Coq_ty -> a1 -> a1) -> Coq_ty -> a1
ty_rec =
  ty_rect

type Ctx x = Datatypes.Coq_list x

data Var t =
   Top (Datatypes.Coq_list t) t
 | Pop (Datatypes.Coq_list t) t t (Var t)

coq_Var_rect :: ((Datatypes.Coq_list a1) -> a1 -> a2) -> ((Datatypes.Coq_list
                a1) -> a1 -> a1 -> (Var a1) -> a2 -> a2) ->
                (Datatypes.Coq_list a1) -> a1 -> (Var a1) -> a2
coq_Var_rect f f0 _ _ v =
  case v of {
   Top _UU0393_ _UU03c4_ -> f _UU0393_ _UU03c4_;
   Pop _UU0393_ _UU03c4_ _UU03c3_ v0 ->
    f0 _UU0393_ _UU03c4_ _UU03c3_ v0 (coq_Var_rect f f0 _UU0393_ _UU03c4_ v0)}

coq_Var_rec :: ((Datatypes.Coq_list a1) -> a1 -> a2) -> ((Datatypes.Coq_list
               a1) -> a1 -> a1 -> (Var a1) -> a2 -> a2) ->
               (Datatypes.Coq_list a1) -> a1 -> (Var a1) -> a2
coq_Var_rec =
  coq_Var_rect

type Var_sig t = Var t

coq_Var_sig_pack :: (Datatypes.Coq_list a1) -> a1 -> (Var a1) -> ( * )
                    (( * ) (Datatypes.Coq_list a1) a1) (Var a1)
coq_Var_sig_pack x x0 var_var =
  (,) ((,) x x0) var_var

coq_Var_Signature :: (Datatypes.Coq_list a1) -> a1 -> Signature.Signature
                     (Var a1) (( * ) (Datatypes.Coq_list a1) a1) (Var_sig a1)
coq_Var_Signature x x0 var_var =
  (,) ((,) x x0) var_var

data Coq_tm =
   Coq_var Coq_ty (Var Coq_ty)
 | Coq_app Coq_ty Coq_ty Coq_tm Coq_tm
 | Coq_abs Coq_ty Coq_ty Coq_tm
 | Coq_build Coq_ty Datatypes.Coq_nat (Fin.Coq_t -> Coq_tm)
 | Coq_get Coq_ty Datatypes.Coq_nat Fin.Coq_t Coq_tm
 | Coq_rval Rdefinitions.RbaseSymbolsImpl__R
 | Coq_add Coq_tm Coq_tm
 | Coq_mul Coq_tm Coq_tm
 | Coq_nsucc Coq_tm
 | Coq_nval Datatypes.Coq_nat
 | Coq_nrec Coq_ty Coq_tm Coq_tm Coq_tm
 | Coq_tuple Coq_ty Coq_ty Coq_tm Coq_tm
 | Coq_first Coq_ty Coq_ty Coq_tm
 | Coq_second Coq_ty Coq_ty Coq_tm
 | Coq_case Coq_ty Coq_ty Coq_ty Coq_tm Coq_tm Coq_tm
 | Coq_inl Coq_ty Coq_ty Coq_tm
 | Coq_inr Coq_ty Coq_ty Coq_tm

tm_rect :: ((Ctx Coq_ty) -> Coq_ty -> (Var Coq_ty) -> a1) -> ((Ctx Coq_ty) ->
           Coq_ty -> Coq_ty -> Coq_tm -> a1 -> Coq_tm -> a1 -> a1) -> ((Ctx
           Coq_ty) -> Coq_ty -> Coq_ty -> Coq_tm -> a1 -> a1) -> ((Ctx
           Coq_ty) -> Coq_ty -> Datatypes.Coq_nat -> (Fin.Coq_t -> Coq_tm) ->
           (Fin.Coq_t -> a1) -> a1) -> ((Ctx Coq_ty) -> Coq_ty ->
           Datatypes.Coq_nat -> Fin.Coq_t -> Coq_tm -> a1 -> a1) -> ((Ctx
           Coq_ty) -> Rdefinitions.RbaseSymbolsImpl__R -> a1) -> ((Ctx
           Coq_ty) -> Coq_tm -> a1 -> Coq_tm -> a1 -> a1) -> ((Ctx Coq_ty) ->
           Coq_tm -> a1 -> Coq_tm -> a1 -> a1) -> ((Ctx Coq_ty) -> Coq_tm ->
           a1 -> a1) -> ((Ctx Coq_ty) -> Datatypes.Coq_nat -> a1) -> ((Ctx
           Coq_ty) -> Coq_ty -> Coq_tm -> a1 -> Coq_tm -> a1 -> Coq_tm -> a1
           -> a1) -> ((Ctx Coq_ty) -> Coq_ty -> Coq_ty -> Coq_tm -> a1 ->
           Coq_tm -> a1 -> a1) -> ((Ctx Coq_ty) -> Coq_ty -> Coq_ty -> Coq_tm
           -> a1 -> a1) -> ((Ctx Coq_ty) -> Coq_ty -> Coq_ty -> Coq_tm -> a1
           -> a1) -> ((Ctx Coq_ty) -> Coq_ty -> Coq_ty -> Coq_ty -> Coq_tm ->
           a1 -> Coq_tm -> a1 -> Coq_tm -> a1 -> a1) -> ((Ctx Coq_ty) ->
           Coq_ty -> Coq_ty -> Coq_tm -> a1 -> a1) -> ((Ctx Coq_ty) -> Coq_ty
           -> Coq_ty -> Coq_tm -> a1 -> a1) -> (Ctx Coq_ty) -> Coq_ty ->
           Coq_tm -> a1
tm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 _UU0393_ _ t =
  case t of {
   Coq_var _UU03c4_ v -> f _UU0393_ _UU03c4_ v;
   Coq_app _UU03c4_ _UU03c3_ t0 t1 ->
    f0 _UU0393_ _UU03c4_ _UU03c3_ t0
      (tm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        _UU0393_ (Arrow _UU03c3_ _UU03c4_) t0) t1
      (tm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        _UU0393_ _UU03c3_ t1);
   Coq_abs _UU03c4_ _UU03c3_ t0 ->
    f1 _UU0393_ _UU03c4_ _UU03c3_ t0
      (tm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        (Datatypes.Coq_cons _UU03c3_ _UU0393_) _UU03c4_ t0);
   Coq_build _UU03c4_ n t0 ->
    f2 _UU0393_ _UU03c4_ n t0 (\t1 ->
      tm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        _UU0393_ _UU03c4_ (t0 t1));
   Coq_get _UU03c4_ n t0 t1 ->
    f3 _UU0393_ _UU03c4_ n t0 t1
      (tm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        _UU0393_ (Array n _UU03c4_) t1);
   Coq_rval r -> f4 _UU0393_ r;
   Coq_add t0 t1 ->
    f5 _UU0393_ t0
      (tm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        _UU0393_ Real t0) t1
      (tm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        _UU0393_ Real t1);
   Coq_mul t0 t1 ->
    f6 _UU0393_ t0
      (tm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        _UU0393_ Real t0) t1
      (tm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        _UU0393_ Real t1);
   Coq_nsucc t0 ->
    f7 _UU0393_ t0
      (tm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        _UU0393_ Nat t0);
   Coq_nval n -> f8 _UU0393_ n;
   Coq_nrec _UU03c4_ t0 t1 t2 ->
    f9 _UU0393_ _UU03c4_ t0
      (tm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        _UU0393_ (Arrow _UU03c4_ _UU03c4_) t0) t1
      (tm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        _UU0393_ Nat t1) t2
      (tm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        _UU0393_ _UU03c4_ t2);
   Coq_tuple _UU03c4_ _UU03c3_ t0 t1 ->
    f10 _UU0393_ _UU03c4_ _UU03c3_ t0
      (tm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        _UU0393_ _UU03c4_ t0) t1
      (tm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        _UU0393_ _UU03c3_ t1);
   Coq_first _UU03c4_ _UU03c3_ t0 ->
    f11 _UU0393_ _UU03c4_ _UU03c3_ t0
      (tm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        _UU0393_ (Prod _UU03c4_ _UU03c3_) t0);
   Coq_second _UU03c4_ _UU03c3_ t0 ->
    f12 _UU0393_ _UU03c4_ _UU03c3_ t0
      (tm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        _UU0393_ (Prod _UU03c4_ _UU03c3_) t0);
   Coq_case _UU03c4_ _UU03c3_ _UU03c1_ t0 t1 t2 ->
    f13 _UU0393_ _UU03c4_ _UU03c3_ _UU03c1_ t0
      (tm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        _UU0393_ (Sum _UU03c4_ _UU03c3_) t0) t1
      (tm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        _UU0393_ (Arrow _UU03c4_ _UU03c1_) t1) t2
      (tm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        _UU0393_ (Arrow _UU03c3_ _UU03c1_) t2);
   Coq_inl _UU03c4_ _UU03c3_ t0 ->
    f14 _UU0393_ _UU03c4_ _UU03c3_ t0
      (tm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        _UU0393_ _UU03c4_ t0);
   Coq_inr _UU03c4_ _UU03c3_ t0 ->
    f15 _UU0393_ _UU03c4_ _UU03c3_ t0
      (tm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        _UU0393_ _UU03c3_ t0)}

tm_rec :: ((Ctx Coq_ty) -> Coq_ty -> (Var Coq_ty) -> a1) -> ((Ctx Coq_ty) ->
          Coq_ty -> Coq_ty -> Coq_tm -> a1 -> Coq_tm -> a1 -> a1) -> ((Ctx
          Coq_ty) -> Coq_ty -> Coq_ty -> Coq_tm -> a1 -> a1) -> ((Ctx 
          Coq_ty) -> Coq_ty -> Datatypes.Coq_nat -> (Fin.Coq_t -> Coq_tm) ->
          (Fin.Coq_t -> a1) -> a1) -> ((Ctx Coq_ty) -> Coq_ty ->
          Datatypes.Coq_nat -> Fin.Coq_t -> Coq_tm -> a1 -> a1) -> ((Ctx
          Coq_ty) -> Rdefinitions.RbaseSymbolsImpl__R -> a1) -> ((Ctx 
          Coq_ty) -> Coq_tm -> a1 -> Coq_tm -> a1 -> a1) -> ((Ctx Coq_ty) ->
          Coq_tm -> a1 -> Coq_tm -> a1 -> a1) -> ((Ctx Coq_ty) -> Coq_tm ->
          a1 -> a1) -> ((Ctx Coq_ty) -> Datatypes.Coq_nat -> a1) -> ((Ctx
          Coq_ty) -> Coq_ty -> Coq_tm -> a1 -> Coq_tm -> a1 -> Coq_tm -> a1
          -> a1) -> ((Ctx Coq_ty) -> Coq_ty -> Coq_ty -> Coq_tm -> a1 ->
          Coq_tm -> a1 -> a1) -> ((Ctx Coq_ty) -> Coq_ty -> Coq_ty -> Coq_tm
          -> a1 -> a1) -> ((Ctx Coq_ty) -> Coq_ty -> Coq_ty -> Coq_tm -> a1
          -> a1) -> ((Ctx Coq_ty) -> Coq_ty -> Coq_ty -> Coq_ty -> Coq_tm ->
          a1 -> Coq_tm -> a1 -> Coq_tm -> a1 -> a1) -> ((Ctx Coq_ty) ->
          Coq_ty -> Coq_ty -> Coq_tm -> a1 -> a1) -> ((Ctx Coq_ty) -> Coq_ty
          -> Coq_ty -> Coq_tm -> a1 -> a1) -> (Ctx Coq_ty) -> Coq_ty ->
          Coq_tm -> a1
tm_rec =
  tm_rect

ex_id_real :: Coq_tm
ex_id_real =
  Coq_abs Real Real (Coq_var Real (Top Datatypes.Coq_nil Real))

ex_const :: Coq_tm
ex_const =
  Coq_abs (Arrow Real Real) Real (Coq_abs Real Real (Coq_var Real (Top
    (Datatypes.Coq_cons Real Datatypes.Coq_nil) Real)))

ex_plus :: (Ctx Coq_ty) -> Coq_tm
ex_plus _UU0393_ =
  Coq_abs (Arrow Real Real) Real (Coq_abs Real Real (Coq_add (Coq_var Real
    (Pop (Datatypes.Coq_cons Real _UU0393_) Real Real (Top _UU0393_ Real)))
    (Coq_var Real (Top (Datatypes.Coq_cons Real _UU0393_) Real))))

ex_square :: (Ctx Coq_ty) -> Coq_tm
ex_square _UU0393_ =
  Coq_abs Real Real (Coq_mul (Coq_var Real (Top _UU0393_ Real)) (Coq_var Real
    (Top _UU0393_ Real)))

square_plus :: (Ctx Coq_ty) -> Coq_tm
square_plus _UU0393_ =
  Coq_app Real Real (Coq_app (Arrow Real Real) Real
    (ex_plus (Datatypes.Coq_cons Real (Datatypes.Coq_cons Real _UU0393_)))
    (Coq_var Real (Pop (Datatypes.Coq_cons Real _UU0393_) Real Real (Top
    _UU0393_ Real)))) (Coq_app Real Real
    (ex_square (Datatypes.Coq_cons Real (Datatypes.Coq_cons Real _UU0393_)))
    (Coq_var Real (Top (Datatypes.Coq_cons Real _UU0393_) Real)))

ex_square_plus :: (Ctx Coq_ty) -> Coq_tm
ex_square_plus _UU0393_ =
  Coq_abs (Arrow Real Real) Real (Coq_abs Real Real (square_plus _UU0393_))

ex_neuron :: Coq_tm
ex_neuron =
  Coq_abs (Arrow Real (Arrow Real Real)) Real (Coq_abs (Arrow Real Real) Real
    (Coq_abs Real Real (Coq_add (Coq_add (Coq_var Real (Pop
    (Datatypes.Coq_cons Real (Datatypes.Coq_cons Real Datatypes.Coq_nil))
    Real Real (Top (Datatypes.Coq_cons Real Datatypes.Coq_nil) Real)))
    (Coq_var Real (Top (Datatypes.Coq_cons Real (Datatypes.Coq_cons Real
    Datatypes.Coq_nil)) Real))) (Coq_var Real (Pop (Datatypes.Coq_cons Real
    (Datatypes.Coq_cons Real Datatypes.Coq_nil)) Real Real (Pop
    (Datatypes.Coq_cons Real Datatypes.Coq_nil) Real Real (Top
    Datatypes.Coq_nil Real)))))))

type Coq_gren = Coq_ty -> (Var Coq_ty) -> Var Coq_ty

type Coq_gsub = Coq_ty -> (Var Coq_ty) -> Coq_tm

type Coq_ren = Coq_ty -> (Var Coq_ty) -> Var Coq_ty

type Coq_sub = Coq_ty -> (Var Coq_ty) -> Coq_tm

id_sub :: (Datatypes.Coq_list Coq_ty) -> Coq_sub
id_sub _ x x0 =
  Coq_var x x0

cons_sub :: (Datatypes.Coq_list Coq_ty) -> (Ctx Coq_ty) -> Coq_ty -> Coq_tm
            -> Coq_sub -> Coq_sub
cons_sub _UU0393_ _ _UU03c4_ e s _ v =
  case v of {
   Top _UU0393_0 _UU03c4_0 ->
    Logic0.transport _UU03c4_ _UU03c4_0 (\_ ->
      Logic0.transport _UU0393_ _UU0393_0 e) __;
   Pop _UU0393_0 _UU03c4_0 _UU03c3_ v0 ->
    Logic0.transport _UU03c4_ _UU03c3_ (\v1 _ ->
      Logic0.transport _UU0393_ _UU0393_0 s _UU03c4_0 v1) v0 __}

data Coq_cons_sub_graph =
   Coq_cons_sub_graph_equation_1 (Datatypes.Coq_list Coq_ty) (Ctx Coq_ty) 
 Coq_ty Coq_tm Coq_sub
 | Coq_cons_sub_graph_equation_2 (Datatypes.Coq_list Coq_ty) (Ctx Coq_ty) 
 Coq_ty Coq_tm Coq_sub Coq_ty (Var Coq_ty)

cons_sub_graph_rect :: ((Datatypes.Coq_list Coq_ty) -> (Ctx Coq_ty) -> Coq_ty
                       -> Coq_tm -> Coq_sub -> a1) -> ((Datatypes.Coq_list
                       Coq_ty) -> (Ctx Coq_ty) -> Coq_ty -> Coq_tm -> Coq_sub
                       -> Coq_ty -> (Var Coq_ty) -> a1) ->
                       (Datatypes.Coq_list Coq_ty) -> (Ctx Coq_ty) -> Coq_ty
                       -> Coq_tm -> Coq_sub -> Coq_ty -> (Var Coq_ty) ->
                       Coq_tm -> Coq_cons_sub_graph -> a1
cons_sub_graph_rect f f0 _ _ _ _ _ _ _ _ c =
  case c of {
   Coq_cons_sub_graph_equation_1 _UU0393_0 _UU0393_' _UU03c4_1 e s ->
    f _UU0393_0 _UU0393_' _UU03c4_1 e s;
   Coq_cons_sub_graph_equation_2 _UU0393_1 _UU0393_' _UU03c3_ e s _UU03c4_2
    v -> f0 _UU0393_1 _UU0393_' _UU03c3_ e s _UU03c4_2 v}

cons_sub_graph_correct :: (Datatypes.Coq_list Coq_ty) -> (Ctx Coq_ty) ->
                          Coq_ty -> Coq_tm -> Coq_sub -> Coq_ty -> (Var
                          Coq_ty) -> Coq_cons_sub_graph
cons_sub_graph_correct _UU0393_ _UU0393_' _UU03c4_ e s _UU03c4_0 v =
  let {v0 = (,) ((,) (Datatypes.Coq_cons _UU03c4_ _UU0393_) _UU03c4_0) v} in
  case Init0.pr2 v0 of {
   Top _ _ ->
    Logic.eq_rect __ (\v1 _ ->
      Logic0.transport (Top _UU0393_ _UU03c4_) v1
        (Logic.eq_rect_r e (Coq_cons_sub_graph_equation_1 _UU0393_ _UU0393_'
          _UU03c4_ e s)
          (cons_sub _UU0393_ _UU0393_' _UU03c4_ e s _UU03c4_ (Top _UU0393_
            _UU03c4_)))) __ v __;
   Pop _ _ _ v1 ->
    Logic0.transport (Pop _UU0393_ _UU03c4_0 _UU03c4_ v1) v
      (Logic.eq_rect_r (s _UU03c4_0 v1) (Coq_cons_sub_graph_equation_2
        _UU0393_ _UU0393_' _UU03c4_ e s _UU03c4_0 v1)
        (cons_sub _UU0393_ _UU0393_' _UU03c4_ e s _UU03c4_0 (Pop _UU0393_
          _UU03c4_0 _UU03c4_ v1)))}

cons_sub_elim :: ((Datatypes.Coq_list Coq_ty) -> (Ctx Coq_ty) -> Coq_ty ->
                 Coq_tm -> Coq_sub -> a1) -> ((Datatypes.Coq_list Coq_ty) ->
                 (Ctx Coq_ty) -> Coq_ty -> Coq_tm -> Coq_sub -> Coq_ty ->
                 (Var Coq_ty) -> a1) -> (Datatypes.Coq_list Coq_ty) -> (Ctx
                 Coq_ty) -> Coq_ty -> Coq_tm -> Coq_sub -> Coq_ty -> (Var
                 Coq_ty) -> a1
cons_sub_elim f f0 _UU0393_ _UU0393_' _UU03c4_ e s _UU03c4_0 v =
  cons_sub_graph_rect f f0 _UU0393_ _UU0393_' _UU03c4_ e s _UU03c4_0 v
    (cons_sub _UU0393_ _UU0393_' _UU03c4_ e s _UU03c4_0 v)
    (cons_sub_graph_correct _UU0393_ _UU0393_' _UU03c4_ e s _UU03c4_0 v)

coq_FunctionalElimination_cons_sub :: ((Datatypes.Coq_list Coq_ty) -> (Ctx
                                      Coq_ty) -> Coq_ty -> Coq_tm -> Coq_sub
                                      -> a1) -> ((Datatypes.Coq_list 
                                      Coq_ty) -> (Ctx Coq_ty) -> Coq_ty ->
                                      Coq_tm -> Coq_sub -> Coq_ty -> (Var
                                      Coq_ty) -> a1) -> (Datatypes.Coq_list
                                      Coq_ty) -> (Ctx Coq_ty) -> Coq_ty ->
                                      Coq_tm -> Coq_sub -> Coq_ty -> (Var
                                      Coq_ty) -> a1
coq_FunctionalElimination_cons_sub =
  cons_sub_elim

coq_FunctionalInduction_cons_sub :: Classes.FunctionalInduction
                                    ((Datatypes.Coq_list Coq_ty) -> (Ctx
                                    Coq_ty) -> Coq_ty -> Coq_tm -> Coq_sub ->
                                    Coq_sub)
coq_FunctionalInduction_cons_sub =
  unsafeCoerce cons_sub_graph_correct

hd_sub :: (Datatypes.Coq_list Coq_ty) -> (Datatypes.Coq_list Coq_ty) ->
          Coq_ty -> Coq_sub -> Coq_tm
hd_sub _UU0393_ _ _UU03c4_ s =
  s _UU03c4_ (Top _UU0393_ _UU03c4_)

tl_sub :: (Datatypes.Coq_list Coq_ty) -> (Datatypes.Coq_list Coq_ty) ->
          Coq_ty -> Coq_sub -> Coq_sub
tl_sub _UU0393_ _ _UU03c4_ s _UU03c3_ x =
  s _UU03c3_ (Pop _UU0393_ _UU03c3_ _UU03c4_ x)

id_ren :: (Datatypes.Coq_list Coq_ty) -> Coq_ren
id_ren _ _ x =
  x

hd_ren :: (Datatypes.Coq_list Coq_ty) -> (Datatypes.Coq_list Coq_ty) ->
          Coq_ty -> Coq_ren -> Var Coq_ty
hd_ren _UU0393_ _ _UU03c4_ r =
  r _UU03c4_ (Top _UU0393_ _UU03c4_)

tl_ren :: (Datatypes.Coq_list Coq_ty) -> (Datatypes.Coq_list Coq_ty) ->
          Coq_ty -> Coq_ren -> Coq_ren
tl_ren _UU0393_ _ _UU03c4_ r _UU03c3_ x =
  r _UU03c3_ (Pop _UU0393_ _UU03c3_ _UU03c4_ x)

rename_lifted :: (Datatypes.Coq_list Coq_ty) -> (Datatypes.Coq_list Coq_ty)
                 -> Coq_ty -> Coq_ren -> Coq_ren
rename_lifted _UU0393_ _UU0393_' _UU03c4_ r _ v =
  case v of {
   Top _UU0393_0 _UU03c4_0 ->
    Logic0.transport _UU03c4_ _UU03c4_0 (\_ ->
      Logic0.transport _UU0393_ _UU0393_0 (Top _UU0393_' _UU03c4_)) __;
   Pop _UU0393_0 _UU03c4_0 _UU03c3_ v0 ->
    Logic0.transport _UU03c4_ _UU03c3_ (\v1 _ ->
      Logic0.transport _UU0393_ _UU0393_0 (\_UU03c4_1 v2 -> Pop _UU0393_'
        _UU03c4_1 _UU03c4_ (r _UU03c4_1 v2)) _UU03c4_0 v1) v0 __}

data Coq_rename_lifted_graph =
   Coq_rename_lifted_graph_equation_1 (Datatypes.Coq_list Coq_ty) (Datatypes.Coq_list
                                                                  Coq_ty) 
 Coq_ty Coq_ren
 | Coq_rename_lifted_graph_equation_2 (Datatypes.Coq_list Coq_ty) (Datatypes.Coq_list
                                                                  Coq_ty) 
 Coq_ty Coq_ren Coq_ty (Var Coq_ty)

rename_lifted_graph_rect :: ((Datatypes.Coq_list Coq_ty) ->
                            (Datatypes.Coq_list Coq_ty) -> Coq_ty -> Coq_ren
                            -> a1) -> ((Datatypes.Coq_list Coq_ty) ->
                            (Datatypes.Coq_list Coq_ty) -> Coq_ty -> Coq_ren
                            -> Coq_ty -> (Var Coq_ty) -> a1) ->
                            (Datatypes.Coq_list Coq_ty) ->
                            (Datatypes.Coq_list Coq_ty) -> Coq_ty -> Coq_ren
                            -> Coq_ty -> (Var Coq_ty) -> (Var Coq_ty) ->
                            Coq_rename_lifted_graph -> a1
rename_lifted_graph_rect f f0 _ _ _ _ _ _ _ r =
  case r of {
   Coq_rename_lifted_graph_equation_1 _UU0393_0 _UU0393_' _UU03c4_1 r0 ->
    f _UU0393_0 _UU0393_' _UU03c4_1 r0;
   Coq_rename_lifted_graph_equation_2 _UU0393_1 _UU0393_' _UU03c3_ r0
    _UU03c4_2 v -> f0 _UU0393_1 _UU0393_' _UU03c3_ r0 _UU03c4_2 v}

rename_lifted_graph_correct :: (Datatypes.Coq_list Coq_ty) ->
                               (Datatypes.Coq_list Coq_ty) -> Coq_ty ->
                               Coq_ren -> Coq_ty -> (Var Coq_ty) ->
                               Coq_rename_lifted_graph
rename_lifted_graph_correct _UU0393_ _UU0393_' _UU03c4_ r _UU03c4_0 v =
  let {v0 = (,) ((,) (Datatypes.Coq_cons _UU03c4_ _UU0393_) _UU03c4_0) v} in
  case Init0.pr2 v0 of {
   Top _ _ ->
    Logic.eq_rect __ (\v1 _ ->
      Logic0.transport (Top _UU0393_ _UU03c4_) v1
        (Logic.eq_rect_r (Top _UU0393_' _UU03c4_)
          (Coq_rename_lifted_graph_equation_1 _UU0393_ _UU0393_' _UU03c4_ r)
          (rename_lifted _UU0393_ _UU0393_' _UU03c4_ r _UU03c4_ (Top _UU0393_
            _UU03c4_)))) __ v __;
   Pop _ _ _ v1 ->
    Logic0.transport (Pop _UU0393_ _UU03c4_0 _UU03c4_ v1) v
      (Logic.eq_rect_r (Pop _UU0393_' _UU03c4_0 _UU03c4_ (r _UU03c4_0 v1))
        (Coq_rename_lifted_graph_equation_2 _UU0393_ _UU0393_' _UU03c4_ r
        _UU03c4_0 v1)
        (rename_lifted _UU0393_ _UU0393_' _UU03c4_ r _UU03c4_0 (Pop _UU0393_
          _UU03c4_0 _UU03c4_ v1)))}

rename_lifted_elim :: ((Datatypes.Coq_list Coq_ty) -> (Datatypes.Coq_list
                      Coq_ty) -> Coq_ty -> Coq_ren -> a1) ->
                      ((Datatypes.Coq_list Coq_ty) -> (Datatypes.Coq_list
                      Coq_ty) -> Coq_ty -> Coq_ren -> Coq_ty -> (Var 
                      Coq_ty) -> a1) -> (Datatypes.Coq_list Coq_ty) ->
                      (Datatypes.Coq_list Coq_ty) -> Coq_ty -> Coq_ren ->
                      Coq_ty -> (Var Coq_ty) -> a1
rename_lifted_elim f f0 _UU0393_ _UU0393_' _UU03c4_ r _UU03c4_0 v =
  rename_lifted_graph_rect f f0 _UU0393_ _UU0393_' _UU03c4_ r _UU03c4_0 v
    (rename_lifted _UU0393_ _UU0393_' _UU03c4_ r _UU03c4_0 v)
    (rename_lifted_graph_correct _UU0393_ _UU0393_' _UU03c4_ r _UU03c4_0 v)

coq_FunctionalElimination_rename_lifted :: ((Datatypes.Coq_list Coq_ty) ->
                                           (Datatypes.Coq_list Coq_ty) ->
                                           Coq_ty -> Coq_ren -> a1) ->
                                           ((Datatypes.Coq_list Coq_ty) ->
                                           (Datatypes.Coq_list Coq_ty) ->
                                           Coq_ty -> Coq_ren -> Coq_ty ->
                                           (Var Coq_ty) -> a1) ->
                                           (Datatypes.Coq_list Coq_ty) ->
                                           (Datatypes.Coq_list Coq_ty) ->
                                           Coq_ty -> Coq_ren -> Coq_ty ->
                                           (Var Coq_ty) -> a1
coq_FunctionalElimination_rename_lifted =
  rename_lifted_elim

coq_FunctionalInduction_rename_lifted :: Classes.FunctionalInduction
                                         ((Datatypes.Coq_list Coq_ty) ->
                                         (Datatypes.Coq_list Coq_ty) ->
                                         Coq_ty -> Coq_ren -> Coq_ren)
coq_FunctionalInduction_rename_lifted =
  unsafeCoerce rename_lifted_graph_correct

rename :: (Datatypes.Coq_list Coq_ty) -> (Datatypes.Coq_list Coq_ty) ->
          Coq_ty -> Coq_ren -> Coq_tm -> Coq_tm
rename _UU0393_ _UU0393_' _ r t =
  case t of {
   Coq_var _UU03c4_0 v -> Coq_var _UU03c4_0 (r _UU03c4_0 v);
   Coq_app _UU03c4_0 _UU03c3_ t1 t2 -> Coq_app _UU03c4_0 _UU03c3_
    (rename _UU0393_ _UU0393_' (Arrow _UU03c3_ _UU03c4_0) r t1)
    (rename _UU0393_ _UU0393_' _UU03c3_ r t2);
   Coq_abs _UU03c4_0 _UU03c3_ f -> Coq_abs _UU03c4_0 _UU03c3_
    (rename (Datatypes.Coq_cons _UU03c3_ _UU0393_) (Datatypes.Coq_cons
      _UU03c3_ _UU0393_') _UU03c4_0
      (rename_lifted _UU0393_ _UU0393_' _UU03c3_ r) f);
   Coq_build _UU03c4_0 n ta -> Coq_build _UU03c4_0 n
    (Basics.compose (rename _UU0393_ _UU0393_' _UU03c4_0 r) ta);
   Coq_get _UU03c4_0 n ti ta -> Coq_get _UU03c4_0 n ti
    (rename _UU0393_ _UU0393_' (Array n _UU03c4_0) r ta);
   Coq_add t1 t2 -> Coq_add (rename _UU0393_ _UU0393_' Real r t1)
    (rename _UU0393_ _UU0393_' Real r t2);
   Coq_mul t1 t2 -> Coq_mul (rename _UU0393_ _UU0393_' Real r t1)
    (rename _UU0393_ _UU0393_' Real r t2);
   Coq_nsucc t0 -> Coq_nsucc (rename _UU0393_ _UU0393_' Nat r t0);
   Coq_nrec _UU03c4_0 f i d -> Coq_nrec _UU03c4_0
    (rename _UU0393_ _UU0393_' (Arrow _UU03c4_0 _UU03c4_0) r f)
    (rename _UU0393_ _UU0393_' Nat r i)
    (rename _UU0393_ _UU0393_' _UU03c4_0 r d);
   Coq_tuple _UU03c4_0 _UU03c3_ t1 t2 -> Coq_tuple _UU03c4_0 _UU03c3_
    (rename _UU0393_ _UU0393_' _UU03c4_0 r t1)
    (rename _UU0393_ _UU0393_' _UU03c3_ r t2);
   Coq_first _UU03c4_0 _UU03c3_ p -> Coq_first _UU03c4_0 _UU03c3_
    (rename _UU0393_ _UU0393_' (Prod _UU03c4_0 _UU03c3_) r p);
   Coq_second _UU03c4_0 _UU03c3_ p -> Coq_second _UU03c4_0 _UU03c3_
    (rename _UU0393_ _UU0393_' (Prod _UU03c4_0 _UU03c3_) r p);
   Coq_case _UU03c4_0 _UU03c3_ _UU03c1_ e c1 c2 -> Coq_case _UU03c4_0
    _UU03c3_ _UU03c1_
    (rename _UU0393_ _UU0393_' (Sum _UU03c4_0 _UU03c3_) r e)
    (rename _UU0393_ _UU0393_' (Arrow _UU03c4_0 _UU03c1_) r c1)
    (rename _UU0393_ _UU0393_' (Arrow _UU03c3_ _UU03c1_) r c2);
   Coq_inl _UU03c4_0 _UU03c3_ e -> Coq_inl _UU03c4_0 _UU03c3_
    (rename _UU0393_ _UU0393_' _UU03c4_0 r e);
   Coq_inr _UU03c4_0 _UU03c3_ e -> Coq_inr _UU03c4_0 _UU03c3_
    (rename _UU0393_ _UU0393_' _UU03c3_ r e);
   x -> x}

shift :: (Ctx Coq_ty) -> Coq_ty -> Coq_ty -> Coq_tm -> Coq_tm
shift _UU0393_ _UU03c4_ _UU03c3_ =
  rename _UU0393_ (Datatypes.Coq_cons _UU03c3_ _UU0393_) _UU03c4_
    (\_UU03c1_ x -> Pop _UU0393_ _UU03c1_ _UU03c3_ x)

substitute_lifted :: (Datatypes.Coq_list Coq_ty) -> (Datatypes.Coq_list
                     Coq_ty) -> Coq_ty -> Coq_sub -> Coq_sub
substitute_lifted _UU0393_ _UU0393_' _UU03c4_ s _ v =
  case v of {
   Top _UU0393_0 _UU03c4_0 ->
    Logic0.transport _UU03c4_ _UU03c4_0 (\_ ->
      Logic0.transport _UU0393_ _UU0393_0 (Coq_var _UU03c4_ (Top _UU0393_'
        _UU03c4_))) __;
   Pop _UU0393_0 _UU03c4_0 _UU03c3_ v0 ->
    Logic0.transport _UU03c4_ _UU03c3_ (\v1 _ ->
      Logic0.transport _UU0393_ _UU0393_0 (\_UU03c4_1 v2 ->
        shift _UU0393_' _UU03c4_1 _UU03c4_ (s _UU03c4_1 v2)) _UU03c4_0 v1) v0
      __}

data Coq_substitute_lifted_graph =
   Coq_substitute_lifted_graph_equation_1 (Datatypes.Coq_list Coq_ty) 
 (Datatypes.Coq_list Coq_ty) Coq_ty Coq_sub
 | Coq_substitute_lifted_graph_equation_2 (Datatypes.Coq_list Coq_ty) 
 (Datatypes.Coq_list Coq_ty) Coq_ty Coq_sub Coq_ty (Var Coq_ty)

substitute_lifted_graph_rect :: ((Datatypes.Coq_list Coq_ty) ->
                                (Datatypes.Coq_list Coq_ty) -> Coq_ty ->
                                Coq_sub -> a1) -> ((Datatypes.Coq_list
                                Coq_ty) -> (Datatypes.Coq_list Coq_ty) ->
                                Coq_ty -> Coq_sub -> Coq_ty -> (Var Coq_ty)
                                -> a1) -> (Datatypes.Coq_list Coq_ty) ->
                                (Datatypes.Coq_list Coq_ty) -> Coq_ty ->
                                Coq_sub -> Coq_ty -> (Var Coq_ty) -> Coq_tm
                                -> Coq_substitute_lifted_graph -> a1
substitute_lifted_graph_rect f f0 _ _ _ _ _ _ _ s =
  case s of {
   Coq_substitute_lifted_graph_equation_1 _UU0393_0 _UU0393_' _UU03c4_1 s0 ->
    f _UU0393_0 _UU0393_' _UU03c4_1 s0;
   Coq_substitute_lifted_graph_equation_2 _UU0393_1 _UU0393_' _UU03c3_ s0
    _UU03c4_2 v -> f0 _UU0393_1 _UU0393_' _UU03c3_ s0 _UU03c4_2 v}

substitute_lifted_graph_correct :: (Datatypes.Coq_list Coq_ty) ->
                                   (Datatypes.Coq_list Coq_ty) -> Coq_ty ->
                                   Coq_sub -> Coq_ty -> (Var Coq_ty) ->
                                   Coq_substitute_lifted_graph
substitute_lifted_graph_correct _UU0393_ _UU0393_' _UU03c4_ s _UU03c4_0 v =
  let {v0 = (,) ((,) (Datatypes.Coq_cons _UU03c4_ _UU0393_) _UU03c4_0) v} in
  case Init0.pr2 v0 of {
   Top _ _ ->
    Logic.eq_rect __ (\v1 _ ->
      Logic0.transport (Top _UU0393_ _UU03c4_) v1
        (Logic.eq_rect_r (Coq_var _UU03c4_ (Top _UU0393_' _UU03c4_))
          (Coq_substitute_lifted_graph_equation_1 _UU0393_ _UU0393_' _UU03c4_
          s)
          (substitute_lifted _UU0393_ _UU0393_' _UU03c4_ s _UU03c4_ (Top
            _UU0393_ _UU03c4_)))) __ v __;
   Pop _ _ _ v1 ->
    Logic0.transport (Pop _UU0393_ _UU03c4_0 _UU03c4_ v1) v
      (Logic.eq_rect_r (shift _UU0393_' _UU03c4_0 _UU03c4_ (s _UU03c4_0 v1))
        (Coq_substitute_lifted_graph_equation_2 _UU0393_ _UU0393_' _UU03c4_ s
        _UU03c4_0 v1)
        (substitute_lifted _UU0393_ _UU0393_' _UU03c4_ s _UU03c4_0 (Pop
          _UU0393_ _UU03c4_0 _UU03c4_ v1)))}

substitute_lifted_elim :: ((Datatypes.Coq_list Coq_ty) -> (Datatypes.Coq_list
                          Coq_ty) -> Coq_ty -> Coq_sub -> a1) ->
                          ((Datatypes.Coq_list Coq_ty) -> (Datatypes.Coq_list
                          Coq_ty) -> Coq_ty -> Coq_sub -> Coq_ty -> (Var
                          Coq_ty) -> a1) -> (Datatypes.Coq_list Coq_ty) ->
                          (Datatypes.Coq_list Coq_ty) -> Coq_ty -> Coq_sub ->
                          Coq_ty -> (Var Coq_ty) -> a1
substitute_lifted_elim f f0 _UU0393_ _UU0393_' _UU03c4_ s _UU03c4_0 v =
  substitute_lifted_graph_rect f f0 _UU0393_ _UU0393_' _UU03c4_ s _UU03c4_0 v
    (substitute_lifted _UU0393_ _UU0393_' _UU03c4_ s _UU03c4_0 v)
    (substitute_lifted_graph_correct _UU0393_ _UU0393_' _UU03c4_ s _UU03c4_0
      v)

coq_FunctionalElimination_substitute_lifted :: ((Datatypes.Coq_list Coq_ty)
                                               -> (Datatypes.Coq_list 
                                               Coq_ty) -> Coq_ty -> Coq_sub
                                               -> a1) -> ((Datatypes.Coq_list
                                               Coq_ty) -> (Datatypes.Coq_list
                                               Coq_ty) -> Coq_ty -> Coq_sub
                                               -> Coq_ty -> (Var Coq_ty) ->
                                               a1) -> (Datatypes.Coq_list
                                               Coq_ty) -> (Datatypes.Coq_list
                                               Coq_ty) -> Coq_ty -> Coq_sub
                                               -> Coq_ty -> (Var Coq_ty) ->
                                               a1
coq_FunctionalElimination_substitute_lifted =
  substitute_lifted_elim

coq_FunctionalInduction_substitute_lifted :: Classes.FunctionalInduction
                                             ((Datatypes.Coq_list Coq_ty) ->
                                             (Datatypes.Coq_list Coq_ty) ->
                                             Coq_ty -> Coq_sub -> Coq_sub)
coq_FunctionalInduction_substitute_lifted =
  unsafeCoerce substitute_lifted_graph_correct

substitute :: (Datatypes.Coq_list Coq_ty) -> (Datatypes.Coq_list Coq_ty) ->
              Coq_ty -> Coq_sub -> Coq_tm -> Coq_tm
substitute _UU0393_ _UU0393_' _ s t =
  case t of {
   Coq_var _UU03c4_0 v -> s _UU03c4_0 v;
   Coq_app _UU03c4_0 _UU03c3_ t1 t2 -> Coq_app _UU03c4_0 _UU03c3_
    (substitute _UU0393_ _UU0393_' (Arrow _UU03c3_ _UU03c4_0) s t1)
    (substitute _UU0393_ _UU0393_' _UU03c3_ s t2);
   Coq_abs _UU03c4_0 _UU03c3_ f -> Coq_abs _UU03c4_0 _UU03c3_
    (substitute (Datatypes.Coq_cons _UU03c3_ _UU0393_) (Datatypes.Coq_cons
      _UU03c3_ _UU0393_') _UU03c4_0
      (substitute_lifted _UU0393_ _UU0393_' _UU03c3_ s) f);
   Coq_build _UU03c4_0 n ta -> Coq_build _UU03c4_0 n
    (Basics.compose (substitute _UU0393_ _UU0393_' _UU03c4_0 s) ta);
   Coq_get _UU03c4_0 n ti ta -> Coq_get _UU03c4_0 n ti
    (substitute _UU0393_ _UU0393_' (Array n _UU03c4_0) s ta);
   Coq_add t1 t2 -> Coq_add (substitute _UU0393_ _UU0393_' Real s t1)
    (substitute _UU0393_ _UU0393_' Real s t2);
   Coq_mul t1 t2 -> Coq_mul (substitute _UU0393_ _UU0393_' Real s t1)
    (substitute _UU0393_ _UU0393_' Real s t2);
   Coq_nsucc t0 -> Coq_nsucc (substitute _UU0393_ _UU0393_' Nat s t0);
   Coq_nrec _UU03c4_0 f i d -> Coq_nrec _UU03c4_0
    (substitute _UU0393_ _UU0393_' (Arrow _UU03c4_0 _UU03c4_0) s f)
    (substitute _UU0393_ _UU0393_' Nat s i)
    (substitute _UU0393_ _UU0393_' _UU03c4_0 s d);
   Coq_tuple _UU03c4_0 _UU03c3_ t1 t2 -> Coq_tuple _UU03c4_0 _UU03c3_
    (substitute _UU0393_ _UU0393_' _UU03c4_0 s t1)
    (substitute _UU0393_ _UU0393_' _UU03c3_ s t2);
   Coq_first _UU03c4_0 _UU03c3_ p -> Coq_first _UU03c4_0 _UU03c3_
    (substitute _UU0393_ _UU0393_' (Prod _UU03c4_0 _UU03c3_) s p);
   Coq_second _UU03c4_0 _UU03c3_ p -> Coq_second _UU03c4_0 _UU03c3_
    (substitute _UU0393_ _UU0393_' (Prod _UU03c4_0 _UU03c3_) s p);
   Coq_case _UU03c4_0 _UU03c3_ _UU03c1_ e c1 c2 -> Coq_case _UU03c4_0
    _UU03c3_ _UU03c1_
    (substitute _UU0393_ _UU0393_' (Sum _UU03c4_0 _UU03c3_) s e)
    (substitute _UU0393_ _UU0393_' (Arrow _UU03c4_0 _UU03c1_) s c1)
    (substitute _UU0393_ _UU0393_' (Arrow _UU03c3_ _UU03c1_) s c2);
   Coq_inl _UU03c4_0 _UU03c3_ e -> Coq_inl _UU03c4_0 _UU03c3_
    (substitute _UU0393_ _UU0393_' _UU03c4_0 s e);
   Coq_inr _UU03c4_0 _UU03c3_ e -> Coq_inr _UU03c4_0 _UU03c3_
    (substitute _UU0393_ _UU0393_' _UU03c3_ s e);
   x -> x}

compose_ren_ren :: (Datatypes.Coq_list Coq_ty) -> (Datatypes.Coq_list 
                   Coq_ty) -> (Datatypes.Coq_list Coq_ty) -> Coq_ren ->
                   Coq_ren -> Coq_ren
compose_ren_ren _ _ _ r r' t v =
  r t (r' t v)

compose_sub_ren :: (Datatypes.Coq_list Coq_ty) -> (Datatypes.Coq_list 
                   Coq_ty) -> (Datatypes.Coq_list Coq_ty) -> Coq_sub ->
                   Coq_ren -> Coq_sub
compose_sub_ren _ _ _ s r t v =
  s t (r t v)

compose_ren_sub :: (Datatypes.Coq_list Coq_ty) -> (Datatypes.Coq_list 
                   Coq_ty) -> (Datatypes.Coq_list Coq_ty) -> Coq_ren ->
                   Coq_sub -> Coq_sub
compose_ren_sub _ _UU0393_' _UU0393_'' r s t v =
  rename _UU0393_' _UU0393_'' t r (s t v)

compose_sub_sub :: (Datatypes.Coq_list Coq_ty) -> (Datatypes.Coq_list 
                   Coq_ty) -> (Datatypes.Coq_list Coq_ty) -> Coq_sub ->
                   Coq_sub -> Coq_sub
compose_sub_sub _ _UU0393_' _UU0393_'' s s' t v =
  substitute _UU0393_' _UU0393_'' t s (s' t v)

letin :: (Ctx Coq_ty) -> Coq_ty -> Coq_ty -> Coq_tm -> Coq_tm -> Coq_tm
letin _ _UU03c4_ _UU03c3_ e x =
  Coq_app _UU03c4_ _UU03c3_ (Coq_abs _UU03c4_ _UU03c3_ x) e

ifold :: (Ctx Coq_ty) -> Coq_ty -> Coq_tm -> Coq_tm -> Coq_tm -> Coq_tm
ifold _UU0393_ _UU03c4_ tf n td =
  Coq_nrec _UU03c4_ (Coq_app (Arrow _UU03c4_ _UU03c4_) Nat (Coq_abs (Arrow
    _UU03c4_ _UU03c4_) Nat (Coq_app (Arrow _UU03c4_ _UU03c4_) Nat
    (shift _UU0393_ (Arrow Nat (Arrow _UU03c4_ _UU03c4_)) Nat tf) (Coq_nsucc
    (Coq_var Nat (Top _UU0393_ Nat))))) (Coq_nval Datatypes.O)) n td

vector_hot :: (Datatypes.Coq_list Coq_ty) -> Datatypes.Coq_nat -> Fin.Coq_t
              -> Coq_tm
vector_hot _ n i =
  Coq_build Real n (\j ->
    case Fin.eqb n n i j of {
     Datatypes.Coq_true -> Coq_rval
      (Rdefinitions.coq_IZR (BinNums.Zpos BinNums.Coq_xH));
     Datatypes.Coq_false -> Coq_rval (Rdefinitions.coq_IZR BinNums.Z0)})

vector_map :: (Ctx Coq_ty) -> Coq_ty -> Coq_ty -> Datatypes.Coq_nat -> Coq_tm
              -> Coq_tm -> Coq_tm
vector_map _ _UU03c4_ _UU03c3_ n f a =
  Coq_build _UU03c3_ n (\i -> Coq_app _UU03c3_ _UU03c4_ f (Coq_get _UU03c4_ n
    i a))

vector_map2 :: (Ctx Coq_ty) -> Coq_ty -> Coq_ty -> Coq_ty ->
               Datatypes.Coq_nat -> Coq_tm -> Coq_tm -> Coq_tm -> Coq_tm
vector_map2 _ _UU03c4_ _UU03c3_ _UU03c1_ n a1 a2 f =
  Coq_build _UU03c1_ n (\i -> Coq_app _UU03c1_ _UU03c3_ (Coq_app (Arrow
    _UU03c3_ _UU03c1_) _UU03c4_ f (Coq_get _UU03c4_ n i a1)) (Coq_get
    _UU03c3_ n i a2))

vector_zip :: (Ctx Coq_ty) -> Coq_ty -> Coq_ty -> Datatypes.Coq_nat -> Coq_tm
              -> Coq_tm -> Coq_tm
vector_zip _UU0393_ _UU03c4_ _UU03c3_ n a1 a2 =
  vector_map2 _UU0393_ _UU03c4_ _UU03c3_ (Prod _UU03c4_ _UU03c3_) n a1 a2
    (Coq_abs (Arrow _UU03c3_ (Prod _UU03c4_ _UU03c3_)) _UU03c4_ (Coq_abs
    (Prod _UU03c4_ _UU03c3_) _UU03c3_ (Coq_tuple _UU03c4_ _UU03c3_ (Coq_var
    _UU03c4_ (Pop (Datatypes.Coq_cons _UU03c4_ _UU0393_) _UU03c4_ _UU03c3_
    (Top _UU0393_ _UU03c4_))) (Coq_var _UU03c3_ (Top (Datatypes.Coq_cons
    _UU03c4_ _UU0393_) _UU03c3_)))))

vector_fill :: (Ctx Coq_ty) -> Coq_ty -> Datatypes.Coq_nat -> Coq_tm ->
               Coq_tm
vector_fill _ _UU03c4_ n e =
  Coq_build _UU03c4_ n (\_ -> e)

vector_add :: (Ctx Coq_ty) -> Datatypes.Coq_nat -> Coq_tm -> Coq_tm -> Coq_tm
vector_add _UU0393_ n a1 a2 =
  vector_map2 _UU0393_ Real Real Real n a1 a2 (Coq_abs (Arrow Real Real) Real
    (Coq_abs Real Real (Coq_add (Coq_var Real (Pop (Datatypes.Coq_cons Real
    _UU0393_) Real Real (Top _UU0393_ Real))) (Coq_var Real (Top
    (Datatypes.Coq_cons Real _UU0393_) Real)))))

vector_scale :: (Ctx Coq_ty) -> Datatypes.Coq_nat -> Coq_tm -> Coq_tm ->
                Coq_tm
vector_scale _UU0393_ n s a =
  vector_map _UU0393_ Real Real n (Coq_abs Real Real (Coq_mul
    (shift _UU0393_ Real Real s) (Coq_var Real (Top _UU0393_ Real)))) a

tm_compose :: (Ctx Coq_ty) -> Coq_ty -> Coq_ty -> Coq_ty -> Coq_tm -> Coq_tm
              -> Coq_tm
tm_compose _UU0393_ _UU03c4_ _UU03c3_ _UU03c1_ f g =
  Coq_abs _UU03c1_ _UU03c4_ (Coq_app _UU03c1_ _UU03c3_
    (shift _UU0393_ (Arrow _UU03c3_ _UU03c1_) _UU03c4_ g) (Coq_app _UU03c3_
    _UU03c4_ (shift _UU0393_ (Arrow _UU03c4_ _UU03c3_) _UU03c4_ f) (Coq_var
    _UU03c4_ (Top _UU0393_ _UU03c4_))))

