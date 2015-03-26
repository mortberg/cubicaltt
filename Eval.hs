{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Eval where

import Data.List
import Data.Maybe (fromMaybe)
import Data.Map (Map,(!),mapWithKey,assocs,filterWithKey
                ,elems,intersectionWith,intersection,keys)
import qualified Data.Map as Map

import Connections
import CTT

look :: String -> Env -> Val
look x (Upd rho (y,u)) | x == y    = u
                        | otherwise = look x rho
look x r@(Def rho r1) = case lookup x rho of
  Just (_,t) -> eval r t
  Nothing    -> look x r1
look x (Sub rho _) = look x rho

lookType :: String -> Env -> Val
lookType x (Upd rho (y,VVar _ a)) | x == y    = a
                                  | otherwise = lookType x rho
lookType x r@(Def rho r1) = case lookup x rho of
  Just (a,_) -> eval r a
  Nothing -> lookType x r1
lookType x (Sub rho _) = lookType x rho

lookName :: Name -> Env -> Formula
lookName i (Upd rho _) = lookName i rho
lookName i (Def _ rho) = lookName i rho
lookName i (Sub rho (j,phi)) | i == j    = phi
                             | otherwise = lookName i rho

-----------------------------------------------------------------------
-- Nominal instances

instance Nominal Env where
  support Empty             = []
  support (Upd rho (_,u))   = support u `union` support rho
  support (Sub rho (_,phi)) = support phi `union` support rho
  support (Def _ rho)       = support rho

  act e iphi = mapEnv (`act` iphi) (`act` iphi) e
  swap e ij  = mapEnv (`swap` ij) (`swap` ij) e

instance Nominal Val where
  support VU                    = []
  support (Ter _ e)             = support e
  support (VPi v1 v2)           = support [v1,v2]
  support (VComp a u ts)        = support (a,u,ts)
  support (VIdP a v0 v1)        = support [a,v0,v1]
  support (VPath i v)           = i `delete` support v
  support (VTrans u v)          = support (u,v)
  support (VSigma u v)          = support (u,v)
  support (VPair u v)           = support (u,v)
  support (VFst u)              = support u
  support (VSnd u)              = support u
  support (VCon _ vs)           = support vs
  support (VPCon _ a vs phi)    = support (a,vs,phi)
  support (VVar _ v)            = support v
  support (VApp u v)            = support (u,v)
  support (VAppFormula u phi)   = support (u,phi)
  support (VSplit u v)          = support (u,v)
  support (VGlue a ts)          = support (a,ts)
  support (VGlueElem a ts)      = support (a,ts)
  support (VCompElem a es u us) = support (a,es,u,us)
  support (VElimComp a es u)    = support (a,es,u)

  act u (i, phi) =
    let acti :: Nominal a => a -> a
        acti u = act u (i, phi)
        sphi = support phi
    in case u of
         VU      -> VU
         Ter t e -> Ter t (acti e)
         VPi a f -> VPi (acti a) (acti f)
         VComp a v ts -> compLine (acti a) (acti v) (acti ts)
         VIdP a u v -> VIdP (acti a) (acti u) (acti v)
         VPath j v | j == i -> u
                   | j `notElem` sphi -> VPath j (acti v)
                   | otherwise -> VPath k (acti (v `swap` (j,k)))
              where k = fresh (v, Atom i, phi)
         VTrans u v -> transLine (acti u) (acti v)
         VSigma a f -> VSigma (acti a) (acti f)
         VPair u v  -> VPair (acti u) (acti v)
         VFst u     -> VFst (acti u)
         VSnd u     -> VSnd (acti u)
         VCon c vs  -> VCon c (acti vs)
         VPCon c a vs phi -> pcon c (acti a) (acti vs) (acti phi)
         VVar x v   -> VVar x (acti v)
         VAppFormula u psi -> acti u @@ acti psi
         VApp u v   -> app (acti u) (acti v)
         VSplit u v -> app (acti u) (acti v)
         VGlue a ts -> glue (acti a) (acti ts)
         VGlueElem a ts -> glueElem (acti a) (acti ts)
         VCompElem a es u us -> compElem (acti a) (acti es) (acti u) (acti us)
         VElimComp a es u -> elimComp (acti a) (acti es) (acti u)

  -- This increases efficiency as it won't trigger computation.
  swap u ij@ (i,j) =
    let sw :: Nominal a => a -> a
        sw u = swap u ij
    in case u of
         VU                  -> VU
         Ter t e             -> Ter t (sw e)
         VPi a f             -> VPi (sw a) (sw f)
         VComp a v ts        -> VComp (sw a) (sw v) (sw ts)
         VIdP a u v          -> VIdP (sw a) (sw u) (sw v)
         VPath k v           -> VPath (swapName k ij) (sw v)
         VTrans u v          -> VTrans (sw u) (sw v)
         VSigma a f          -> VSigma (sw a) (sw f)
         VPair u v           -> VPair (sw u) (sw v)
         VFst u              -> VFst (sw u)
         VSnd u              -> VSnd (sw u)
         VCon c vs           -> VCon c (sw vs)
         VPCon c a vs phi    -> VPCon c (sw a) (sw vs) (sw phi)
         VVar x v            -> VVar x (sw v)
         VAppFormula u psi   -> VAppFormula (sw u) (sw psi)
         VApp u v            -> VApp (sw u) (sw v)
         VSplit u v          -> VSplit (sw u) (sw v)
         VGlue a ts          -> VGlue (sw a) (sw ts)
         VGlueElem a ts      -> VGlueElem (sw a) (sw ts)
         VCompElem a es u us -> VCompElem (sw a) (sw es) (sw u) (sw us)
         VElimComp a es u    -> VElimComp (sw a) (sw es) (sw u)

-----------------------------------------------------------------------
-- The evaluator

eval :: Env -> Ter -> Val
eval rho v = case v of
  U                   -> VU
  App r s             -> app (eval rho r) (eval rho s)
  Var i               -> look i rho
  Pi t@(Lam _ a _)    -> VPi (eval rho a) (eval rho t)
  Lam{}               -> Ter v rho
  Sigma t@(Lam _ a _) -> VSigma (eval rho a) (eval rho t)
  Pair a b            -> VPair (eval rho a) (eval rho b)
  Fst a               -> fstVal (eval rho a)
  Snd a               -> sndVal (eval rho a)
  Where t decls       -> eval (Def decls rho) t
  Con name ts         -> VCon name (map (eval rho) ts)
  PCon name a ts phi  -> 
    pcon name (eval rho a) (map (eval rho) ts) (evalFormula rho phi)
  Split{}             -> Ter v rho
  Sum{}               -> Ter v rho
  Undef l             -> error $ "eval: undefined at " ++ show l
  IdP a e0 e1         -> VIdP (eval rho a) (eval rho e0) (eval rho e1)
  Path i t            ->
    let j = fresh rho
    in VPath j (eval (Sub rho (i,Atom j)) t)
  Trans u v        -> transLine (eval rho u) (eval rho v)
  AppFormula e phi -> (eval rho e) @@ (evalFormula rho phi)
  Comp a t0 ts     -> compLine (eval rho a) (eval rho t0) (evalSystem rho ts)
  Glue a ts        -> glue (eval rho a) (evalSystem rho ts)
  GlueElem a ts    -> glueElem (eval rho a) (evalSystem rho ts)
  CompElem a es u us -> compElem (eval rho a) (evalSystem rho es) (eval rho u)
                         (evalSystem rho us)
  ElimComp a es u    -> elimComp (eval rho a) (evalSystem rho es) (eval rho u)

evalFormula :: Env -> Formula -> Formula
evalFormula rho phi = case phi of
  Atom i         -> lookName i rho
  NegAtom i      -> negFormula (lookName i rho)
  phi1 :/\: phi2 -> evalFormula rho phi1 `andFormula` evalFormula rho phi2
  phi1 :\/: phi2 -> evalFormula rho phi1 `orFormula` evalFormula rho phi2
  _              -> phi

evals :: Env -> [(Ident,Ter)] -> [(Ident,Val)]
evals env bts = [ (b,eval env t) | (b,t) <- bts ]

evalSystem :: Env -> System Ter -> System Val
evalSystem rho ts =
  let out = concat [ let betas = meetss [ invFormula (lookName i rho) d
                                        | (i,d) <- assocs alpha ]
                     in [ (beta,eval (rho `face` beta) talpha) | beta <- betas ]
                   | (alpha,talpha) <- assocs ts ]
  in mkSystem out

-- TODO: Write using case-of
app :: Val -> Val -> Val
app (Ter (Lam x _ t) e) u                  = eval (Upd e (x,u)) t
app (Ter (Split _ _ _ nvs) e) (VCon c us) = case lookupBranch c nvs of
  Just (OBranch _ xs t) -> eval (upds e (zip xs us)) t
  _     -> error $ "app: Split with insufficient arguments; " ++
                   " missing case for " ++ c
app u@(Ter Split{} _) v | isNeutral v = VSplit u v
app (Ter (Split _ _ _ nvs) e) (VPCon c _ us phi) = case lookupBranch c nvs of
  Just (PBranch _ xs i t) -> eval (Sub (upds e (zip xs us)) (i,phi)) t
  _ -> error ("app: Split with insufficient arguments; " ++
              " missing case for " ++ c)
app u@(Ter (Split _ _ f hbr) e) kan@(VComp v w ws) =
  let j   = fresh (e,kan)
      wsj = Map.map (@@ j) ws
      ws' = mapWithKey (\alpha -> app (u `face` alpha)) wsj
      w'  = app u w
      ffill = app (eval e f) (fill j v w wsj)
  in genComp j ffill w' ws'

app kan@(VTrans (VPath i (VPi a f)) li0) ui1 =
    let j   = fresh (kan,ui1)
        (aj,fj) = (a,f) `swap` (i,j)
        u   = transFillNeg j aj ui1
        ui0 = transNeg j aj ui1
    in trans j (app fj u) (app li0 ui0)
app kan@(VComp (VPi a f) li0 ts) ui1 =
    let j   = fresh (kan,ui1)
        tsj = Map.map (@@ j) ts
    in comp j (app f ui1) (app li0 ui1)
              (intersectionWith app tsj (border ui1 tsj))
app r s | isNeutral r = VApp r s
app _ _ = error "app"

fstVal, sndVal :: Val -> Val
fstVal (VPair a b)    = a
fstVal u | isNeutral u = VFst u
sndVal (VPair a b)    = b
sndVal u | isNeutral u = VSnd u

-- infer the type of a neutral value
inferType :: Val -> Val
inferType v = case v of
  VVar _ t -> t
  VFst t -> case inferType t of
    VSigma a _ -> a
    ty         -> error $ "inferType: expected Sigma type for " ++ show v
                  ++ ", got " ++ show ty
  VSnd t -> case inferType t of
    VSigma _ f -> app f (VFst t)
    ty         -> error $ "inferType: expected Sigma type for " ++ show v
                  ++ ", got " ++ show ty
  VSplit (Ter (Split _ _ f _) rho) v1 -> app (eval rho f) v1
  VApp t0 t1 -> case inferType t0 of
    VPi _ f -> app f t1
    ty      -> error $ "inferType: expected Pi type for " ++ show v
               ++ ", got " ++ show ty
  VAppFormula t phi -> case inferType t of
    VIdP a _ _ -> a @@ phi
    ty         -> error $ "inferType: expected IdP type for " ++ show v
                  ++ ", got " ++ show ty
  VComp a _ _ -> a
  VTrans a _  -> a @@ One
  _ -> error $ "inferType: not neutral " ++ show v

(@@) :: ToFormula a => Val -> a -> Val
(VPath i u) @@ phi = u `act` (i,toFormula phi)
-- (KanUElem _ u) @@ phi = u @@ phi
v @@ phi | isNeutral v = case (inferType v,toFormula phi) of
  (VIdP  _ a0 _,Dir 0) -> a0
  (VIdP  _ _ a1,Dir 1) -> a1
  _  -> VAppFormula v (toFormula phi)
v @@ phi = error $ "(@@): " ++ show v ++ " should be neutral."

pcon :: LIdent -> Val -> [Val] -> Formula -> Val
pcon c a@(Ter (Sum _ _ lbls) rho) us phi = case lookupPLabel c lbls of
  Just (tele,t0,t1) | phi == Dir 0 -> eval (updsTele rho tele us) t0
                    | phi == Dir 1 -> eval (updsTele rho tele us) t1
                    | otherwise -> VPCon c a us phi
  Nothing           -> error "pcon"
-- pcon c a us phi     = VPCon c a us phi

-----------------------------------------------------------
-- Transport

transLine :: Val -> Val -> Val
transLine u v = trans i (u @@ i) v
  where i = fresh (u,v)

transNegLine :: Val -> Val -> Val
transNegLine u v = transNeg i (u @@ i) v
  where i = fresh (u,v)

trans :: Name -> Val -> Val -> Val
trans i v0 v1 | i `notElem` support v0 = v1
trans i v0 v1 = case (v0,v1) of
  (VIdP a u v,w) ->
    let j   = fresh (Atom i, v0, w)
        ts' = mkSystem [(j ~> 0,u),(j ~> 1,v)]
    in VPath j $ genComp i (a @@ j) (w @@ j) ts'
  (VSigma a f,u) ->
    let (u1,u2) = (fstVal u,sndVal u)
        fill_u1 = transFill i a u1
        ui1     = trans i a u1
        comp_u2 = trans i (app f fill_u1) u2
    in VPair ui1 comp_u2
  (VPi{},_) -> VTrans (VPath i v0) v1
  (Ter (Sum _ _ nass) env,VCon c us) -> case lookupLabel c nass of
    Just as -> VCon c $ transps i as env us
    Nothing -> error $ "trans: missing constructor " ++ c ++ " in " ++ show v0
  (Ter (Sum _ _ nass) env,VPCon c _ ws0 phi) -> case lookupLabel c nass of
    -- v1 should be independent of i, so i # phi
    Just as -> VPCon c (v0 `face` (i ~> 1)) (transps i as env ws0) phi
    Nothing -> error $ "trans: missing path constructor " ++ c ++
                       " in " ++ show v0
  _ | isNeutral v0 || isNeutral v1 -> VTrans (VPath i v0) v1
  (Ter (Sum _ _ nass) env,VComp b w ws) -> comp k v01 (trans i v0 w) ws'
    where v01 = v0 `face` (i ~> 1)  -- b is vi0 and independent of j
          k   = fresh (v0,v1,Atom i)
          transp alpha w = trans i (v0 `face` alpha) (w @@ k)
          ws'          = mapWithKey transp ws

  (VGlue a ts,_)    -> transGlue i a ts v1
  (VComp VU a es,_) -> transU i a es v1
  _ | otherwise -> error $ "trans not implemented for v0 = " ++ show v0
                   ++ "\n and v1 = " ++ show v1

transNeg :: Name -> Val -> Val -> Val
transNeg i a u = trans i (a `sym` i) u

transFill, transFillNeg :: Name -> Val -> Val -> Val
transFill i a u = trans j (a `conj` (i,j)) u
  where j = fresh (Atom i,a,u)
transFillNeg i a u = (transFill i (a `sym` i) u) `sym` i

transps :: Name -> [(Ident,Ter)] -> Env -> [Val] -> [Val]
transps i []         _ []     = []
transps i ((x,a):as) e (u:us) =
  let v   = transFill i (eval e a) u
      vi1 = trans i (eval e a) u
      vs  = transps i as (Upd e (x,v)) us
  in vi1 : vs
transps _ _ _ _ = error "transps: different lengths of types and values"

-- Given u of type a "squeeze i a u" connects in the direction i
-- trans i a u(i=0) to u(i=1)
squeeze :: Name -> Val -> Val -> Val
squeeze i a u = trans j (a `disj` (i,j)) u
  where j = fresh (Atom i,a,u)

squeezeNeg :: Name -> Val -> Val -> Val
squeezeNeg i a u = transNeg j (a `conj` (i,j)) u
  where j = fresh (Atom i,a,u)

-------------------------------------------------------------------------------
-- Composition

compLine :: Val -> Val -> System Val -> Val
compLine a u ts = comp i a u (Map.map (@@ i) ts)
  where i = fresh (a,u,ts)

genComp, genCompNeg :: Name -> Val -> Val -> System Val -> Val
genComp i a u ts | Map.null ts = trans i a u
genComp i a u ts = comp i ai1 (trans i a u) ts'
  where ai1 = a `face` (i ~> 1)
        ts' = mapWithKey (\alpha -> squeeze i (a `face` alpha)) ts
genCompNeg i a u ts = genComp i (a `sym` i) u (ts `sym` i)

fill, fillNeg :: Name -> Val -> Val -> System Val -> Val
fill i a u ts = comp j a u (ts `conj` (i,j))
  where j = fresh (Atom i,a,u,ts)
fillNeg i a u ts = (fill i a u (ts `sym` i)) `sym` i

genFill, genFillNeg :: Name -> Val -> Val -> System Val -> Val
genFill i a u ts = genComp j (a `conj` (i,j)) u (ts `conj` (i,j))
  where j = fresh (Atom i,a,u,ts)
genFillNeg i a u ts = (genFill i (a `sym` i) u (ts `sym` i)) `sym` i

comps :: Name -> [(Ident,Ter)] -> Env -> [(System Val,Val)] -> [Val]
comps i []         _ []         = []
comps i ((x,a):as) e ((ts,u):tsus) =
  let v   = genFill i (eval e a) u ts
      vi1 = genComp i (eval e a) u ts
      vs  = comps i as (Upd e (x,v)) tsus
  in vi1 : vs
comps _ _ _ _ = error "comps: different lengths of types and values"

-- i is independent of a and u
comp :: Name -> Val -> Val -> System Val -> Val
comp i a u ts | eps `Map.member` ts    = (ts ! eps) `face` (i ~> 1)
comp i a u ts | i `notElem` support ts = u
comp i a u ts | not (Map.null indep)   = comp i a u ts'
  where (ts',indep) = Map.partition (\t -> i `elem` support t) ts
comp i a u ts = let j = fresh (Atom i,a,u,ts) -- maybe only in vid??
                in case a of
  VIdP p _ _ -> VPath j $ comp i (p @@ j) (u @@ j) (Map.map (@@ j) ts)
  VSigma a f -> VPair ui1 comp_u2
    where (t1s, t2s) = (Map.map fstVal ts, Map.map sndVal ts)
          (u1,  u2)  = (fstVal u, sndVal u)
          fill_u1    = fill i a u1 t1s
          ui1        = comp i a u1 t1s
          comp_u2    = genComp i (app f fill_u1) u2 t2s
  VPi{} -> VComp a u (Map.map (VPath i) ts)
  VU -> VComp VU u (Map.map (VPath i) ts)
  _ | isNeutral a || isNeutralSystem ts || isNeutral u ->
    VComp a u (Map.map (VPath i) ts)
  VGlue b hisos -> compGlue i b hisos u ts
  VComp VU a es -> compU i a es u ts
  Ter (Sum _ _ nass) env -> case u of
    VCon n us -> case lookupLabel n nass of
      Just as ->
        if all isCon (elems ts)
           then let tsus = transposeSystemAndList (Map.map unCon ts) us
                in VCon n $ comps i as env tsus
           else VComp a u (Map.map (VPath i) ts)
      Nothing -> error $ "comp: missing constructor in labelled sum " ++ n
    VPCon{} -> VComp a u (Map.map (VPath i) ts)
    _ -> error "comp ter sum"

compNeg :: Name -> Val -> Val -> System Val -> Val
compNeg i a u ts = comp i a u (ts `sym` i)

-- fills :: Name -> [(Ident,Ter)] -> Env -> [(System Val,Val)] -> [Val]
-- fills i []         _ []         = []
-- fills i ((x,a):as) e ((ts,u):tsus) =
--   let v  = genFill i (eval e a) ts u
--       vs = fills i as (Upd e (x,v)) tsus
--   in v : vs
-- fills _ _ _ _ = error "fills: different lengths of types and values"

-------------------------------------------------------------------------------
-- | Glue
--
-- An hiso for a type b is a five-tuple: (a,f,g,r,s)   where
--  a : U
--  f : a -> b
--  g : b -> a
--  s : forall (y : b), f (g y) = y
--  t : forall (x : a), g (f x) = x

hisoDom :: Val -> Val
hisoDom (VPair a _) = a
hisoDom x           = error $ "HisoDom: Not an hiso: " ++ show x

hisoFun :: Val -> Val
hisoFun (VPair _ (VPair f _)) = f
hisoFun x                     = error $ "HisoFun: Not an hiso: " ++ show x

glue :: Val -> System Val -> Val
glue b ts | Map.null ts         = b
          | eps `Map.member` ts = hisoDom (ts ! eps)
          | otherwise           = VGlue b ts

glueElem :: Val -> System Val -> Val
glueElem v us | Map.null us         = v
              | eps `Map.member` us = us ! eps
              | otherwise           = VGlueElem v us

unGlue :: System Val -> Val -> Val
unGlue hisos w
    | Map.null hisos         = w
    | eps `Map.member` hisos = app (hisoFun (hisos ! eps)) w
    | otherwise              = case w of
       VGlueElem v us   -> v
--       KanUElem _ v    -> app g v
       _ -> error $ "unGlue: " ++ show w ++ " should be neutral!"

transGlue :: Name -> Val -> System Val -> Val -> Val
transGlue i b hisos wi0 = glueElem vi1'' usi1
  where vi0  = unGlue (hisos `face` (i ~> 0)) wi0 -- in b(i0)

        vi1  = trans i b vi0           -- in b(i1)

        hisosI1 = hisos `face` (i ~> 1)
        hisos'' =
          filterWithKey (\alpha _ -> alpha `Map.notMember` hisos) hisosI1

        -- set of elements in hisos independent of i
        hisos' = filterWithKey (\alpha _ -> i `Map.notMember` alpha) hisos

        us'    = mapWithKey (\gamma isoG ->
                  transFill i (hisoDom isoG) (wi0 `face` gamma))
                 hisos'
        usi1'  = mapWithKey (\gamma isoG ->
                   trans i (hisoDom isoG) (wi0 `face` gamma))
                 hisos'

        ls'    = mapWithKey (\gamma isoG ->
                   VPath i $ squeeze i (b `face` gamma)
                           ((hisoFun isoG) `app` (us' ! gamma)))
                 hisos'
        bi1    = b `face` (i ~> 1)
        vi1'   = compLine bi1 vi1 ls'

        uls''   = mapWithKey (\gamma isoG ->
                     gradLemma (bi1 `face` gamma) isoG (usi1' `face` gamma)
                               (vi1' `face` gamma))
                   hisos''

        vi1''   = compLine bi1 vi1' (Map.map snd uls'')

        usi1    = mapWithKey (\gamma _ ->
                    if gamma `Map.member` usi1'
                       then usi1' ! gamma
                       else fst (uls'' ! gamma))
                  hisosI1

compGlue :: Name -> Val -> System Val -> Val -> System Val -> Val
compGlue i b hisos wi0 ws = glueElem vi1' usi1'
  where vs   = mapWithKey
                 (\alpha wAlpha -> unGlue (hisos `face` alpha) wAlpha) ws
        vi0  = unGlue hisos wi0 -- in b

        v    = fill i b vi0 vs           -- in b
        vi1  = comp i b vi0 vs           -- in b

        us'    = mapWithKey (\gamma isoG ->
                   fill i (hisoDom isoG) (wi0 `face` gamma) (ws `face` gamma))
                 hisos
        usi1'  = mapWithKey (\gamma isoG ->
                   comp i (hisoDom isoG) (wi0 `face` gamma) (ws `face` gamma))
                 hisos

        ls'    = mapWithKey (\gamma isoG ->
                   pathComp i (b `face` gamma) (v `face` gamma)
                   (hisoFun isoG `app` (us' ! gamma)) (vs `face` gamma))
                 hisos

        vi1'  = compLine b vi1 ls'

-- assumes u and u' : A are solutions of us + (i0 -> u(i0))
-- The output is an L-path in A(i1) between u(i1) and u'(i1)
pathComp :: Name -> Val -> Val -> Val -> System Val -> Val
pathComp i a u u' us = VPath j $ comp i a (u `face` (i ~> 0)) us'
  where j   = fresh (Atom i, a, us, u, u')
        us' = insertsSystem [(j ~> 0, u), (j ~> 1, u')] us


-- Grad Lemma, takes a iso an L-system ts a value v s.t. sigma us = border v
-- outputs u s.t. border u = us and an L-path between v and sigma u
-- an theta is a L path if L-border theta is constant
gradLemma :: Val -> Val -> System Val -> Val -> (Val, Val)
gradLemma b hiso@(VPair a (VPair f (VPair g (VPair s t)))) us v = (u, VPath i theta'')
  where i:j:_   = freshs (a,hiso,us,v)
        us'     = mapWithKey (\alpha uAlpha ->
                                   app (t `face` alpha) uAlpha @@ i) us
        theta   = fill i a (app g v) us'
        u       = comp i a (app g v) us'
        ws      = insertSystem (i ~> 1) (app t u @@ j) $
                  mapWithKey
                    (\alpha uAlpha ->
                      app (t `face` alpha) uAlpha @@ (Atom i :/\: Atom j)) us
        theta'  = compNeg j a theta ws
        xs      = insertSystem (i ~> 0) (app s v @@ j) $
                  insertSystem (i ~> 1) (app s (app f u) @@ j) $
                  mapWithKey
                    (\alpha uAlpha ->
                      app (s `face` alpha) (app (f `face` alpha) uAlpha) @@ j) us
        theta'' = comp j b (app f theta') xs


-------------------------------------------------------------------------------
-- | Composition in the Universe

compElem :: Val -> System Val -> Val -> System Val -> Val
compElem a es u us | Map.null es         = u
                   | eps `Map.member` us = us ! eps
                   | otherwise           = VCompElem a es u us

elimComp ::Val -> System Val -> Val -> Val
elimComp a es u | Map.null es         = u
                | eps `Map.member` es = transNegLine (es ! eps) u
                | otherwise           = VElimComp a es u

compU :: Name -> Val -> System Val -> Val -> System Val -> Val
compU i a es w0 ws =
    let vs = mapWithKey
               (\alpha -> elimComp (a `face` alpha) (es `face` alpha)) ws
        v0 = elimComp a es w0 -- in a
        v1 = comp i a v0 vs -- in a

        us1' = mapWithKey (\gamma eGamma ->
                            comp i (eGamma @@ One) (w0 `face` gamma)
                                   (ws `face` gamma)) es
        ls' = mapWithKey (\gamma _ -> pathUniv i (es `proj` gamma)
                                      (ws `face` gamma) (w0 `face` gamma))
                 es

        v1' = compLine a v1 ls'
    in compElem a es v1' us1'

-- Computes a homotopy between the image of the composition, and the
-- composition of the image. Given e (an equality in U), an L-system
-- us (in e0) and ui0 (in e0 (i0)) The output is an L(i1)-path in
-- e1(i1) between vi1 and sigma (i1) ui1 where
--   sigma = appEq
--   ui1 = comp i (e 0) us ui0
--   vi1 = comp i (e 1) (sigma us) (sigma(i0) ui0)
-- Moreover, if e is constant, so is the output.
pathUniv :: Name -> Val -> System Val -> Val -> Val
pathUniv i e us ui0 = VPath k xi1
  where j:k:_ = freshs (Atom i,e,us,ui0)
        ej    = e @@ j
        ui1   = genComp i (e @@ Zero) ui0 us
        ws    = mapWithKey (\alpha uAlpha ->
                  transFill j (ej `face` alpha) uAlpha)
                us
        wi0   = transFill j (ej `face` (i ~> 0)) ui0
        wi1   = genComp i ej wi0 ws
        wi1'  = transFill j (ej `face` (i ~> 1)) ui1
        xi1   = genComp j (ej `face` (i ~> 1)) ui1
                  (mkSystem [(k ~> 1, wi1'), (k ~> 0, wi1)])

transU :: Name -> Val -> System Val -> Val -> Val
transU i a es wi0 =
  let vi0 = elimComp (a `face` (i ~> 0)) (es `face` (i ~> 0)) wi0 -- in a(i0)
      vi1 = trans i a vi0      -- in a(i1)

      ai1  = a `face` (i ~> 1)
      esi1 = es `face` (i ~> 1)

      -- gamma in es'' iff i not in the domain of gamma and (i1)gamma in es
      es'' = filterWithKey (\alpha _ -> alpha `Map.notMember` es) esi1

      -- set of faces alpha of es such i is not the domain of alpha
      es'  = filterWithKey (\alpha _ -> i `Map.notMember` alpha) es

      usi1' = mapWithKey (\gamma eGamma ->
                trans i (eGamma @@ One) (wi0 `face` gamma)) es'

      ls' = mapWithKey (\gamma _ ->
              pathUnivTrans i (es `proj` gamma) (wi0 `face` gamma))
--                         pathUniv i (es `proj` gamma) Map.empty (wi0 `face` gamma))
            es'

      vi1' = compLine ai1 vi1 ls'

      uls'' = mapWithKey (\gamma _ -> -- Should be !, not proj ?
                eqLemma (es ! (gamma `meet` (i ~> 1)))
                        (usi1' `face` gamma) (vi1' `face` gamma)) es''

      vi1'' = compLine ai1 vi1' (Map.map snd uls'')

      usi1  = mapWithKey (\gamma _ ->
                if gamma `Map.member` usi1' then usi1' ! gamma
                else fst (uls'' ! gamma)) esi1
  in compElem ai1 esi1 vi1'' usi1

pathUnivTrans :: Name -> Val -> Val -> Val
pathUnivTrans i e ui0 = VPath j xi1
  where j    = fresh (Atom i,e,ui0)
        ej   = e @@ j
        wi0  = transFill j (ej `face` (i ~> 0)) ui0
        wi1  = trans i ej wi0
        xi1  = squeezeNeg j (ej `face` (i ~> 1)) wi1

-- Any equality defines an equivalence.
eqLemma :: Val -> System Val -> Val -> (Val, Val)
eqLemma e ts a = (t,VPath j theta'')
  where i:j:_   = freshs (e,ts,a)
        ei      = e @@ i
        vs      = mapWithKey (\alpha uAlpha ->
                    transFillNeg i (ei `face` alpha) uAlpha) ts
        theta   = genFill i ei a vs
        t       = genComp i ei a vs
        theta'  = transFillNeg i ei t
        ws      = insertSystem (j ~> 1) theta' $
                  insertSystem (j ~> 0) theta $ vs
        theta'' = genCompNeg i ei t ws


-------------------------------------------------------------------------------
-- | Conversion

class Convertible a where
  conv :: Int -> a -> a -> Bool

isIndep :: (Nominal a, Convertible a) => Int -> Name -> a -> Bool
isIndep k i u = conv k u (u `face` (i ~> 0))

isCompSystem :: (Nominal a, Convertible a) => Int -> System a -> Bool
isCompSystem k ts = and [ conv k (getFace alpha beta) (getFace beta alpha)
                        | (alpha,beta) <- allCompatible (keys ts) ]
    where getFace a b = face (ts ! a) (b `minus` a)

instance Convertible Val where
  conv k u v | u == v    = True
             | otherwise =
    let j = fresh (u,v)
    in case (simplify k j u, simplify k j v) of
      (Ter (Lam x a u) e,Ter (Lam x' a' u') e') ->
        let v = mkVar k (eval e a)
        in conv (k+1) (eval (Upd e (x,v)) u) (eval (Upd e' (x',v)) u')
      (Ter (Lam x a u) e,u') ->
        let v = mkVar k (eval e a)
        in conv (k+1) (eval (Upd e (x,v)) u) (app u' v)
      (u',Ter (Lam x a u) e) ->
        let v = mkVar k (eval e a)
        in conv (k+1) (app u' v) (eval (Upd e (x,v)) u)
      (Ter (Split _ p _ _) e,Ter (Split _ p' _ _) e') -> (p == p') && conv k e e'
      (Ter (Sum p _ _) e,Ter (Sum p' _ _) e')     -> (p == p') && conv k e e'
      (Ter (Undef p) e,Ter (Undef p') e')         -> (p == p') && conv k e e'
      (VPi u v,VPi u' v') ->
        let w = mkVar k u
        in conv k u u' && conv (k+1) (app v w) (app v' w)
      (VSigma u v,VSigma u' v') ->
        let w = mkVar k u
        in conv k u u' && conv (k+1) (app v w) (app v' w)
      (VCon c us,VCon c' us')   -> (c == c') && conv k us us'
      (VPair u v,VPair u' v') -> conv k u u' && conv k v v'
      (VPair u v,w)            -> conv k u (fstVal w) && conv k v (sndVal w)
      (w,VPair u v)            -> conv k (fstVal w) u && conv k (sndVal w) v
      (VFst u,VFst u')          -> conv k u u'
      (VSnd u,VSnd u')          -> conv k u u'
      (VApp u v,VApp u' v')     -> conv k u u' && conv k v v'
      (VSplit u v,VSplit u' v') -> conv k u u' && conv k v v'
      (VVar x _, VVar x' _)     -> x == x'
      (VIdP a b c,VIdP a' b' c') -> conv k a a' && conv k b b' && conv k c c'
      (VPath i a,VPath i' a')    -> conv k (a `swap` (i,j)) (a' `swap` (i',j))
      (VPath i a,p')             -> conv k (a `swap` (i,j)) (p' @@ j)
      (p,VPath i' a')            -> conv k (p @@ j) (a' `swap` (i',j))
      (VTrans p u,VTrans p' u') -> conv k p p' && conv k u u'
      (VAppFormula u x,VAppFormula u' x') -> conv k (u,x) (u',x')
      (VComp a u ts,VComp a' u' ts') -> conv k (a,u,ts) (a',u',ts')
      (VGlue v hisos,VGlue v' hisos') -> conv k (v,hisos) (v',hisos')
      (VGlueElem u us,VGlueElem u' us') -> conv k (u,us) (u',us')
      (VCompElem a es u us,VCompElem a' es' u' us') ->
        conv k (a,es,u,us) (a',es',u',us')
      (VElimComp a es u,VElimComp a' es' u') -> conv k (a,es,u) (a',es',u')
      _                         -> False

simplify :: Int -> Name -> Val -> Val
simplify k j v = case v of
  VTrans p u | isIndep k j (p @@ j) -> simplify k j u
  VComp a u ts ->
    let (ts',indep) = Map.partition (\t -> isIndep k j (t @@ j)) ts
    in if Map.null ts' then simplify k j u else VComp a u ts'
  VCompElem a es u us ->
    let (es',indep) = Map.partition (\e -> isIndep k j (e @@ j)) es
        us'         = intersection us es'
    in if Map.null es' then simplify k j u else VCompElem a es' u us'
  VElimComp a es u ->
    let (es',indep) = Map.partition (\e -> isIndep k j (e @@ j)) es
        u' = simplify k j u
    in if Map.null es' then u' else case u' of
      VCompElem _ _ w _ -> simplify k j w
      _ -> VElimComp a es' u'
  _ -> v

instance Convertible Env where
  conv k e e' = conv k (valAndFormulaOfEnv e) (valAndFormulaOfEnv e')

instance Convertible () where
  conv _ _ _ = True

instance (Convertible a, Convertible b) => Convertible (a, b) where
  conv k (u, v) (u', v') = conv k u u' && conv k v v'

instance (Convertible a, Convertible b, Convertible c)
      => Convertible (a, b, c) where
  conv k (u, v, w) (u', v', w') = conv k (u,(v,w)) (u',(v',w'))

instance (Convertible a,Convertible b,Convertible c,Convertible d)
      => Convertible (a,b,c,d) where
  conv k (u,v,w,x) (u',v',w',x') = conv k (u,v,(w,x)) (u',v',(w',x'))

instance Convertible a => Convertible [a] where
  conv k us us' = length us == length us' &&
                  and [conv k u u' | (u,u') <- zip us us']

instance Convertible a => Convertible (System a) where
  conv k ts ts' = keys ts == keys ts' &&
                  and (elems (intersectionWith (conv k) ts ts'))

instance Convertible Formula where
  conv _ phi psi = sort (invFormula phi 1) == sort (invFormula psi 1)
