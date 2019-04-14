module Z.TwoSided

import Z.Interface

%default total

data ZTy : Type where
  ZZ   : ZTy
  ZPos : (k : Nat) -> ZTy
  ZNeg : (k : Nat) -> ZTy

ztySucc : ZTy -> ZTy
ztySucc ZZ = ZPos Z
ztySucc (ZPos k) = ZPos (S k)
ztySucc (ZNeg Z) = ZZ
ztySucc (ZNeg (S k)) = ZNeg k

ZInt ZTy where
  zz = ZZ
  zs k = ztySucc k

VerifiedSucc ZTy where
  EqZ k1 k2 = k1 = k2
  succInjective ZZ ZZ Refl = Refl
  succInjective ZZ (ZPos _) Refl impossible
  succInjective ZZ (ZNeg Z) Refl impossible
  succInjective ZZ (ZNeg (S _)) Refl impossible
  succInjective (ZPos _) ZZ Refl impossible
  succInjective (ZPos k) (ZPos k) Refl = Refl
  succInjective (ZPos _) (ZNeg Z) Refl impossible
  succInjective (ZPos _) (ZNeg (S _)) Refl impossible
  succInjective (ZNeg _) ZZ Refl impossible
  succInjective (ZNeg _) (ZPos _) Refl impossible
  succInjective (ZNeg Z) (ZNeg Z) Refl = Refl
  succInjective (ZNeg Z) (ZNeg (S _)) Refl impossible
  succInjective (ZNeg (S _)) (ZNeg Z) Refl impossible
  succInjective (ZNeg (S k)) (ZNeg (S k)) Refl = Refl

  succSurjective ZZ = (ZNeg Z ** Refl)
  succSurjective (ZPos Z) = (ZZ ** Refl)
  succSurjective (ZPos (S k)) = (ZPos k ** Refl)
  succSurjective (ZNeg k) = (ZNeg (S k) ** Refl)

SidedInduction : (Nat -> ZTy) -> Type
SidedInduction ctor = { prop : ZTy -> Type } ->
                      (prf0 : prop ZZ) ->
                      (prfStep : (k : ZTy) -> prop k -> (prop (zs k), prop (zp k))) ->
                      (k : Nat) ->
                      prop (ctor k)

posInduction : SidedInduction ZPos
posInduction prf0 prfStep Z = fst $ prfStep ZZ prf0
posInduction prf0 prfStep (S k) = fst $ prfStep (ZPos k) (posInduction prf0 prfStep k)

negInduction : SidedInduction ZNeg
negInduction prf0 prfStep Z = snd $ prfStep ZZ prf0
negInduction prf0 prfStep (S k) = snd $ prfStep (ZNeg k) (negInduction prf0 prfStep k)

VerifiedZInt ZTy where
  induction prf0 prfStep ZZ = prf0
  induction prf0 prfStep (ZPos k) = posInduction prf0 prfStep k
  induction prf0 prfStep (ZNeg k) = negInduction prf0 prfStep k
