module Z.TwoSided

import Z.Interface

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
