module ZInt.Interface

%hide Prelude.pred

%default total

%access public export

interface ZInt ty where
  zz : ty
  zs : ty -> ty

%name ZInt k, k1, k2

interface ZInt ty => VerifiedZInt ty where
  succInjective  : (k1, k2 : ty) -> (zs k1 = zs k2) -> k1 = k2
  succSurjective : (k : ty) -> (k' ** zs k' = k)

%name VerifiedZInt k, k1, k2

zp : VerifiedZInt ty => ty -> ty
zp k = fst $ succSurjective k

succPredId : VerifiedZInt zTy => (k : zTy) -> zs (zp k) = k
succPredId k = snd $ succSurjective k

predSuccId : VerifiedZInt zTy => (k : zTy) -> zp (zs k) = k
predSuccId k = succInjective _ _ $ snd $ succSurjective (zs k)
