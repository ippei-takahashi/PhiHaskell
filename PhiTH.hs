{-# LANGUAGE TemplateHaskell #-}
module PhiTH where
import Phi
import Language.Haskell.TH
import Control.Applicative
import Control.Monad

deriveAlgWithName :: Name -> String -> Q [Dec]
deriveAlgWithName dName newName = do
  DataD _ name vars cons _ <- normInfo <$> reify dName
  let
    arg      = appsT $ conT name : map (varT . tvName) vars
    argD     = appT (conT ''D) arg
    var      = varT $ mkName "b"
    dbody    = deriveF arg var cons
    fcons    = mkName newName
    fdest    = mkName $ "un" ++ newName
    dcon     = recC fcons [varStrictType fdest $ strictType notStrict dbody]
    typeD    = newtypeInstD (cxt []) ''D [arg, var] dcon [''Eq, ''Ord, ''Show, ''Read]
    typeF    = tySynInstD ''F [arg] $ argD
    instFnct = mkInst ''Functor argD [deriveFmap fcons fdest var dbody]
    instIA   = mkInst ''InitialAlgebra arg [deriveOut fcons cons]
    instFC   = mkInst ''FinalCoalgebra arg [deriveInn fdest cons] 
  sequence [typeD, typeF, instFnct, instIA, instFC]

mkInst :: Name -> TypeQ -> [DecQ] -> DecQ
mkInst n arg = instanceD (cxt []) (appT (conT n) arg)

deriveAlg :: Name -> Q [Dec]
deriveAlg = prod deriveAlgWithName . (id /\ ("F" ++) . nameBase)

normInfo :: Info -> Dec
normInfo (TyConI datDec) =
  case datDec of
    d@(DataD _ _ _ _ _) -> d
    NewtypeD cxt name vars con derivs -> DataD cxt name vars [con] derivs
normInfo _               = bot

appsT :: [TypeQ] -> TypeQ
appsT []       = bot
appsT [x]      = x
appsT (x:y:zs) = appsT ((appT x y) : zs)

tvName :: TyVarBndr -> Name
tvName (PlainTV n)    = n
tvname (KindedTV n _) = n

deriveF :: TypeQ -> TypeQ -> [Con] -> TypeQ
deriveF from to = reduce (appName ''(:+:)) bot . map (conProd from to)

deriveInn :: Name -> [Con] -> DecQ
deriveInn n xs = do
  name <- sequence $ (map $ const $ newName "f") xs
  mems <- sequence $ map (uncurry conInn) $ zip name xs
  let
    f n x y = infixE (Just x) (varE n) (Just y)
  body <- normalB $ flip (f '(.)) (varE n) $ reduce (f '(\/)) bot $ map varE name
  return $ ValD (VarP 'inn) body mems

deriveOut :: Name -> [Con] -> DecQ
deriveOut n xs = funD 'out cls where
  cls               = map (prod conOut) $ pzip $ (mkPref /\ id) xs
  mkPref [_]        = [conE n]
  mkPref xs         = map (f (conE n)) $ mkPrefSub xs
  mkPrefSub (_:[_]) = [(conE 'Inl), (conE 'Inr)]
  mkPrefSub (_:xs)  = (conE 'Inl) : (map (f (conE 'Inr)) $ mkPrefSub xs)
  f x y          = infixE (Just x) (varE '(.)) (Just y)

deriveFmap :: Name -> Name -> TypeQ -> TypeQ -> DecQ
deriveFmap cons dest v t = funD 'fmap [cls] where
  cls = do
    name <- newName "f"
    let
      f x y = infixE (Just x) (varE '(.)) (Just y)
      core  = liftM3 deriveFmapSub (varE name) v t
      body  = normalB $ f (conE cons) $ f core $ varE dest
    clause [varP name] body []

deriveFmapSub :: Exp -> Type -> Type -> Exp
deriveFmapSub exp v = h where
  h z@(AppT (AppT (ConT n) x) y) 
    | n == ''(:+:) = f '(-|-) x $ h y
    | n == ''(:*:) = f '(><) x $ h y
    | otherwise    = g z 0
  h x              = g x 0
  f n x y = InfixE (Just $ g x 0) (VarE n) (Just y)
  g x t
    | x == v    = times (AppE (VarE 'fmap)) exp t
    | otherwise = case x of
        AppT _ z -> g z (t + 1)
        _        -> VarE 'id 
    

conProd :: TypeQ -> TypeQ -> Con -> TypeQ
conProd from to = processCon $ const $ listProd from to

conInn :: Name -> Con -> DecQ
conInn n = processCon $ listInn n

conOut :: ExpQ -> Con -> ClauseQ
conOut p = processCon $ listOut p
  
processCon :: (Name -> [TypeQ] -> c) -> Con -> c
processCon f (NormalC n xs) = f n $ map return2 xs where 
processCon f (RecC n xs)    = f n $ map return3 xs where 
processCon f (InfixC x n y) = f n [(return2 x), (return2 y)] where 

return2 (_, x) = return x
return3 (_, _, x) = return x

listProd :: TypeQ -> TypeQ -> [TypeQ] -> TypeQ
listProd from to = reduce (appName ''(:*:)) (conT ''()) . map (liftM3 replaceType from to)

replaceType :: Type -> Type -> Type -> Type
replaceType x y = h where
  h z 
    | (x == z)  = y
    | otherwise = case z of
        AppT s t -> AppT s $ h t
        _        -> z

listInn :: Name -> Name -> [TypeQ] -> DecQ
listInn n1 n2 = f where
  f [] = valD (varP n1) (normalB $ appE (varE 'const) $ conE n2) []
  f xs = do
    n <- sequence $ (map $ const $ newName "x") xs
    let 
      g (p :*: e) = clause [s p] (t e) []
      s           = reduce (flip infixP '(:*:)) bot
      t           = normalB . appsE . (:) (conE n2) 
    c <- g $ (map varP /\ map varE) n
    return $ FunD n1 [c]

listOut :: ExpQ -> Name -> [TypeQ] -> ClauseQ
listOut p n xs = do
  name <- sequence $ (map $ const $ newName "x") xs
  pat  <- conP n $ map varP name
  let 
    f x y = infixE (Just x) (conE '(:*:)) (Just y)
  body <- normalB $ appE p $ reduce f (conE '()) $ map varE name
  return $ Clause [pat] body []

appName :: Name -> TypeQ -> TypeQ -> TypeQ
appName n x y =  appT (appT (conT n) x) y

reduce :: (a -> a -> a) -> a -> [a] -> a
reduce _ d []     = d
reduce _ _ [x]    = x
reduce f d (x:xs) = f x $ reduce f d xs

times :: (a -> a) -> a -> Int -> a
times f x = h where
  h 0 = x
  h t = f $ h (t - 1)


