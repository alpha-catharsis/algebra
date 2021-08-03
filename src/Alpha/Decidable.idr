---------------------
-- Module declaration
---------------------

module Alpha.Decidable

---------------
-- Decision not
---------------

public export
decNot : Dec prf -> Dec (Not prf)
decNot (No contra) = Yes contra
decNot (Yes prf) = No (\f => f prf)

--------------
-- Decision or
--------------

public export
decOr : Dec lprf -> Dec rprf -> Dec (Either lprf rprf)
decOr ldec rdec = case ldec of
  Yes lprf => Yes (Left lprf)
  No lcontra => case rdec of
    Yes rprf => Yes (Right rprf)
    No rcontra => No (\ex => case ex of
      Left lx => lcontra lx
      Right rx => rcontra rx)

---------------
-- Decision and
---------------

public export
decAnd : Dec lprf -> Dec rprf -> Dec (lprf, rprf)
decAnd ldec rdec = case ldec of
  No lcontra => No (\x => lcontra (fst x))
  Yes lprf => case rdec of
    No rcontra => No (\x => rcontra (snd x))
    Yes rprf => Yes (lprf, rprf)
