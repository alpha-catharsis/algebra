---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Fn.Fn

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set

----------------------
-- Function definition
----------------------

-- public export
-- 0 FnTy : Set domTy a => Set codTy b => domTy -> codTy -> Type -> Type -> Type
-- FnTy dom cod a b = SetProvenElem dom -> SetProvenElem cod

-- public export
-- interface Set domTy a => Set codTy b => Fn t domTy codTy a b | t where
--   dom : t -> domTy
--   cod : t -> codTy
--   ap : (f : t) -> FnTy (dom f) (cod f) a b
