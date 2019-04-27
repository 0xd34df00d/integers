module ZInt.Interface

%hide Prelude.pred

%default total

%access public export

interface ZInt ty where
  zz : ty
  zs : ty -> ty

%name ZInt k, k1, k2

interface ZInt ty => VerifiedSucc ty where
  EqZ            : (k1, k2 : ty) -> Type
  succInjective  : (k1, k2 : ty) -> (zs k1 `EqZ` zs k2) -> k1 `EqZ` k2
  succSurjective : (k : ty) -> (k' ** zs k' `EqZ` k)


%name VerifiedSucc k, k1, k2

zp : VerifiedSucc ty => ty -> ty
zp k = fst $ succSurjective k

succPredId : VerifiedSucc zTy => (k : zTy) -> zs (zp k) `EqZ` k
succPredId k = snd $ succSurjective k

predSuccId : VerifiedSucc zTy => (k : zTy) -> zp (zs k) `EqZ` k
predSuccId k = succInjective (zp $ zs k) k $ snd $ succSurjective (zs k)

interface VerifiedSucc ty => VerifiedZInt ty where
  induction : { prop : ty -> Type } ->
              (prf0 : (k : ty) -> (k `EqZ` ZInt.Interface.zz) -> prop k) ->
              (prfStep : (k : ty) -> prop k -> (prop (zs k), prop (zp k))) ->
              (k : ty) ->
              prop k
