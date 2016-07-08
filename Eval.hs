{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Eval where

import Data.List
import Data.Maybe (fromMaybe)
import Data.Map (Map,(!),mapWithKey,assocs,filterWithKey
                ,elems,intersectionWith,intersection,keys
                ,member,notMember,empty)
import qualified Data.Map as Map

import Connections
import CTT

-----------------------------------------------------------------------
-- Lookup functions

look :: [Name] -> String -> Env -> Val
look is x (Upd y rho,v:vs,fs,os) | x == y = v
                                 | otherwise = look is x (rho,vs,fs,os)
look is x r@(Def decls rho,vs,fs,Nameless os) = case lookup x decls of
  Just (_,t) -> eval is r t
  Nothing    -> look is x (rho,vs,fs,Nameless os)
look is x (Sub _ rho,vs,_:fs,os) = look is x (rho,vs,fs,os)
look is x (Empty,_,_,_) = error $ "look: not found " ++ show x

lookType :: [Name] -> String -> Env -> Val
lookType is x (Upd y rho,v:vs,fs,os)
  | x /= y        = lookType is x (rho,vs,fs,os)
  | VVar _ a <- v = a
  | otherwise     = error ""
lookType is x r@(Def decls rho,vs,fs,os) = case lookup x decls of
  Just (a,_) -> eval is r a
  Nothing -> lookType is x (rho,vs,fs,os)
lookType is x (Sub _ rho,vs,_:fs,os) = lookType is x (rho,vs,fs,os)
lookType is x (Empty,_,_,_)          = error $ "lookType: not found " ++ show x

lookName :: Name -> Env -> Formula
lookName i (Upd _ rho,v:vs,fs,os) = lookName i (rho,vs,fs,os)
lookName i (Def _ rho,vs,fs,os)   = lookName i (rho,vs,fs,os)
lookName i (Sub j rho,vs,phi:fs,os) | i == j    = phi
                                    | otherwise = lookName i (rho,vs,fs,os)
lookName i _ = error $ "lookName: not found " ++ show i


-----------------------------------------------------------------------
-- Nominal instances

instance Nominal Ctxt where
  support _ = []
  act _ e _ = e
  swap e _  = e

instance Nominal Val where
  support v = case v of
    VU                      -> []
    Ter _ e                 -> support e
    VPi u v                 -> support [u,v]
    VComp a u ts            -> support (a,u,ts)
    VPathP a v0 v1          -> support [a,v0,v1]
    VPLam i v               -> i `delete` support v
    VSigma u v              -> support (u,v)
    VPair u v               -> support (u,v)
    VFst u                  -> support u
    VSnd u                  -> support u
    VCon _ vs               -> support vs
    VPCon _ a vs phis       -> support (a,vs,phis)
    VHComp a u ts           -> support (a,u,ts)
    VVar _ v                -> support v
    VOpaque _ v             -> support v
    VApp u v                -> support (u,v)
    VLam _ u v              -> support (u,v)
    VAppFormula u phi       -> support (u,phi)
    VSplit u v              -> support (u,v)
    VGlue a ts              -> support (a,ts)
    VGlueElem a ts          -> support (a,ts)
    VUnGlueElem a ts        -> support (a,ts)
    VCompU a ts             -> support (a,ts)
    VUnGlueElemU a b es     -> support (a,b,es)

  act is u (i, phi) | i `notElem` support u = u  -- TODO: fix
                    | otherwise =
    let acti :: Nominal a => a -> a
        acti u = act is u (i, phi)
        sphi = support phi
    in case u of
         VU           -> VU
         Ter t e      -> Ter t (acti e)
         VPi a f      -> VPi (acti a) (acti f)
         VComp a v ts -> compLine is (acti a) (acti v) (acti ts)
         VPathP a u v -> VPathP (acti a) (acti u) (acti v)
         VPLam j v | j == i -> u
                   | j `notElem` sphi -> VPLam j (act (j:is) v (i,phi))
                   | otherwise -> VPLam k (act (j:k:is) (v `swap` (j,k)) (i,phi))
              where k = fresh (v,Atom i,phi) -- TODO: fix
         VSigma a f              -> VSigma (acti a) (acti f)
         VPair u v               -> VPair (acti u) (acti v)
         VFst u                  -> fstVal (acti u)
         VSnd u                  -> sndVal (acti u)
         VCon c vs               -> VCon c (acti vs)
         VPCon c a vs phis       -> pcon is c (acti a) (acti vs) (acti phis)
         VHComp a u us           -> hComp is (acti a) (acti u) (acti us)
         VVar x v                -> VVar x (acti v)
         VOpaque x v             -> VOpaque x (acti v)
         VAppFormula u psi       -> appFormula is (acti u) (acti psi)
         VApp u v                -> app is (acti u) (acti v)
         VLam x t u              -> VLam x (acti t) (acti u)
         VSplit u v              -> app is (acti u) (acti v)
         VGlue a ts              -> glue (acti a) (acti ts)
         VGlueElem a ts          -> glueElem (acti a) (acti ts)
         VUnGlueElem a ts        -> unglueElem is (acti a) (acti ts)
         VUnGlueElemU a b es     -> unGlueU is (acti a) (acti b) (acti es)
         VCompU a ts             -> compUniv is (acti a) (acti ts)

  -- This increases efficiency as it won't trigger computation.
  swap u ij@(i,j) =
    let sw :: Nominal a => a -> a
        sw u = swap u ij
    in case u of
         VU                      -> VU
         Ter t e                 -> Ter t (sw e)
         VPi a f                 -> VPi (sw a) (sw f)
         VComp a v ts            -> VComp (sw a) (sw v) (sw ts)
         VPathP a u v            -> VPathP (sw a) (sw u) (sw v)
         VPLam k v               -> VPLam (swapName k ij) (sw v)
         VSigma a f              -> VSigma (sw a) (sw f)
         VPair u v               -> VPair (sw u) (sw v)
         VFst u                  -> VFst (sw u)
         VSnd u                  -> VSnd (sw u)
         VCon c vs               -> VCon c (sw vs)
         VPCon c a vs phis       -> VPCon c (sw a) (sw vs) (sw phis)
         VHComp a u us           -> VHComp (sw a) (sw u) (sw us)
         VVar x v                -> VVar x (sw v)
         VOpaque x v             -> VOpaque x (sw v)
         VAppFormula u psi       -> VAppFormula (sw u) (sw psi)
         VApp u v                -> VApp (sw u) (sw v)
         VLam x u v              -> VLam x (sw u) (sw v)
         VSplit u v              -> VSplit (sw u) (sw v)
         VGlue a ts              -> VGlue (sw a) (sw ts)
         VGlueElem a ts          -> VGlueElem (sw a) (sw ts)
         VUnGlueElem a ts        -> VUnGlueElem (sw a) (sw ts)
         VUnGlueElemU a b es     -> VUnGlueElemU (sw a) (sw b) (sw es)
         VCompU a ts             -> VCompU (sw a) (sw ts)


-----------------------------------------------------------------------
-- The evaluator

eval :: [Name] -> Env -> Ter -> Val
eval is rho@(_,_,_,Nameless os) v = case v of
  U                   -> VU
  App r s             -> app is (eval is rho r) (eval is rho s)
  Var i
    | i `elem` os     -> VOpaque i (lookType is i rho)
    | otherwise       -> look is i rho
  Pi t@(Lam _ a _)    -> VPi (eval is rho a) (eval is rho t)
  Sigma t@(Lam _ a _) -> VSigma (eval is rho a) (eval is rho t)
  Pair a b            -> VPair (eval is rho a) (eval is rho b)
  Fst a               -> fstVal (eval is rho a)
  Snd a               -> sndVal (eval is rho a)
  Where t decls       -> eval is (defWhere decls rho) t
  Con name ts         -> VCon name (map (eval is rho) ts)
  PCon name a ts phis ->
    pcon is name (eval is rho a) (map (eval is rho) ts) (map (evalFormula rho) phis)
  Lam{}               -> Ter v rho
  Split{}             -> Ter v rho
  Sum{}               -> Ter v rho
  HSum{}              -> Ter v rho
  Undef{}             -> Ter v rho
  Hole{}              -> Ter v rho
  PathP a e0 e1       -> VPathP (eval is rho a) (eval is rho e0) (eval is rho e1)
  PLam i t            -> let j = fresh rho -- gensym is   -- Anders: add i??
                         in VPLam j (eval (j:is) (sub (i,Atom j) rho) t)
  AppFormula e phi    -> appFormula is (eval is rho e) (evalFormula rho phi)
  Comp a t0 ts        ->
    compLine is (eval is rho a) (eval is rho t0) (evalSystem is rho ts)
  Fill a t0 ts        ->
    fillLine is (eval is rho a) (eval is rho t0) (evalSystem is rho ts)
  Glue a ts           -> glue (eval is rho a) (evalSystem is rho ts)
  GlueElem a ts       -> glueElem (eval is rho a) (evalSystem is rho ts)
  UnGlueElem a ts     -> unglueElem is (eval is rho a) (evalSystem is rho ts)
  _                   -> error $ "Cannot evaluate " ++ show v

evals :: [Name] -> Env -> [(Ident,Ter)] -> [(Ident,Val)]
evals is env bts = [ (b,eval is env t) | (b,t) <- bts ]

evalFormula :: Env -> Formula -> Formula
evalFormula rho phi = case phi of
  Atom i         -> lookName i rho
  NegAtom i      -> negFormula (lookName i rho)
  phi1 :/\: phi2 -> evalFormula rho phi1 `andFormula` evalFormula rho phi2
  phi1 :\/: phi2 -> evalFormula rho phi1 `orFormula` evalFormula rho phi2
  _              -> phi

evalSystem :: [Name] -> Env -> System Ter -> System Val
evalSystem is rho ts =
  let out = concat [ let betas = meetss [ invFormula (lookName i rho) d
                                        | (i,d) <- assocs alpha ]
                     in [ (beta,eval is (face is rho beta) talpha) | beta <- betas ]
                   | (alpha,talpha) <- assocs ts ]
  in mkSystem out

app :: [Name] -> Val -> Val -> Val
app is u v = case (u,v) of
  (Ter (Lam x _ t) e,_)               -> eval is (upd (x,v) e) t
  (Ter (Split _ _ _ nvs) e,VCon c vs) -> case lookupBranch c nvs of
    Just (OBranch _ xs t) -> eval is (upds (zip xs vs) e) t
    _     -> error $ "app: missing case in split for " ++ c
  (Ter (Split _ _ _ nvs) e,VPCon c _ us phis) -> case lookupBranch c nvs of
    Just (PBranch _ xs is' t) ->
        eval is (subs (zip is' phis) (upds (zip xs us) e)) t -- Anders: add is'?
    _ -> error $ "app: missing case in split for " ++ c
  (Ter (Split _ _ ty hbr) e,VHComp a w ws) -> case eval is e ty of
    VPi _ f -> let j   = fresh (e,v) -- gensym is
                   is' = j:is
                   wsj = Map.map (\u -> appFormula is' u j) ws
                   w'  = app is' u w
                   ws' = mapWithKey (\alpha -> app is' (face is' u alpha)) wsj
                   -- a should be constant
               in comp is' j (app is' f (fill is' j a w wsj)) w' ws'
    _ -> error $ "app: Split annotation not a Pi type " ++ show u
  (Ter Split{} _,_) | isNeutral v         -> VSplit u v
  (VComp (VPLam i (VPi a f)) li0 ts,vi1) ->
    let j       = fresh (u,vi1) -- gensym is
        is'     = j:is
        (aj,fj) = (a,f) `swap` (i,j)
        tsj     = Map.map (\t -> appFormula is' t j) ts
        v       = transFillNeg is' j aj vi1
        vi0     = transNeg is' j aj vi1
    in comp is' j (app is' fj v) (app is' li0 vi0)
                  (intersectionWith (app is') tsj (border is' v tsj))
  _ | isNeutral u       -> VApp u v
  _                     -> error $ "app \n  " ++ show u ++ "\n  " ++ show v

fstVal, sndVal :: Val -> Val
fstVal (VPair a b)     = a
fstVal u | isNeutral u = VFst u
fstVal u               = error $ "fstVal: " ++ show u ++ " is not neutral."
sndVal (VPair a b)     = b
sndVal u | isNeutral u = VSnd u
sndVal u               = error $ "sndVal: " ++ show u ++ " is not neutral."

-- infer the type of a neutral value
inferType :: [Name] -> Val -> Val
inferType is v = case v of
  VVar _ t -> t
  VOpaque _ t -> t
  Ter (Undef _ t) rho -> eval is rho t
  VFst t -> case inferType is t of
    VSigma a _ -> a
    ty         -> error $ "inferType: expected Sigma type for " ++ show v
                  ++ ", got " ++ show ty
  VSnd t -> case inferType is t of
    VSigma _ f -> app is f (VFst t)
    ty         -> error $ "inferType: expected Sigma type for " ++ show v
                  ++ ", got " ++ show ty
  VSplit s@(Ter (Split _ _ t _) rho) v1 -> case eval is rho t of
    VPi _ f -> app is f v1
    ty      -> error $ "inferType: Pi type expected for split annotation in "
               ++ show v ++ ", got " ++ show ty
  VApp t0 t1 -> case inferType is t0 of
    VPi _ f -> app is f t1
    ty      -> error $ "inferType: expected Pi type for " ++ show v
               ++ ", got " ++ show ty
  VAppFormula t phi -> case inferType is t of
    VPathP a _ _ -> appFormula is a phi
    ty         -> error $ "inferType: expected PathP type for " ++ show v
                  ++ ", got " ++ show ty
  VComp a _ _ -> appFormula is a One
--  VUnGlueElem _ b _  -> b   -- This is wrong! Store the type??
  VUnGlueElemU _ b _ -> b
  _ -> error $ "inferType: not neutral " ++ show v

appFormula :: ToFormula a => [Name] -> Val -> a -> Val
appFormula is (VPLam i u) phi         = act is u (i,toFormula phi)
appFormula is v@(Ter Hole{} _) phi    = VAppFormula v (toFormula phi)
appFormula is v phi | isNeutral v     = case (inferType is v,toFormula phi) of
  (VPathP _ a0 _,Dir 0) -> a0
  (VPathP _ _ a1,Dir 1) -> a1
  _                    -> VAppFormula v (toFormula phi)
appFormula _ v phi                   = error $ "appFormula: " ++ show v ++ " should be neutral."

-- Applying a *fresh* name.
(@@@) :: Val -> Name -> Val
(VPLam i u) @@@ j = u `swap` (i,j)
v @@@ j           = VAppFormula v (toFormula j)


-------------------------------------------------------------------------------
-- Composition and filling

comp :: [Name] -> Name -> Val -> Val -> System Val -> Val
comp is i a u ts | eps `member` ts = face is (ts ! eps) (i ~> 1)
comp is i a u ts = case a of
  VPathP p v0 v1 ->
    let j = fresh (Atom i,a,u,ts) -- gensym (i:is)
        is' = j : is
    in VPLam j $ comp is' i (appFormula is' p j) (appFormula is' u j) $
         insertsSystem [(j ~> 0,v0),(j ~> 1,v1)]
           (Map.map (\t -> appFormula is' t j) ts)
  VSigma a f -> VPair ui1 comp_u2
    where (t1s, t2s) = (Map.map fstVal ts, Map.map sndVal ts)
          (u1,  u2)  = (fstVal u, sndVal u)
          fill_u1    = fill is i a u1 t1s
          ui1        = comp is i a u1 t1s
          comp_u2    = comp is i (app is f fill_u1) u2 t2s
  VPi{} -> VComp (VPLam i a) u (Map.map (VPLam i) ts)
  VU -> compUniv is u (Map.map (VPLam i) ts)
  VCompU a es | not (isNeutralU is i es u ts)  -> compU is i a es u ts
  VGlue b equivs | not (isNeutralGlue is i equivs u ts) -> compGlue is i b equivs u ts
  Ter (Sum _ _ nass) env -> case u of
    VCon n us | all isCon (elems ts) -> case lookupLabel n nass of
      Just as -> let tsus = transposeSystemAndList (Map.map unCon ts) us
                 in VCon n $ comps is i as env tsus
      Nothing -> error $ "comp: missing constructor in labelled sum " ++ n
    _ -> VComp (VPLam i a) u (Map.map (VPLam i) ts)
  Ter (HSum _ _ nass) env -> compHIT is i a u ts
  _ -> VComp (VPLam i a) u (Map.map (VPLam i) ts)

compNeg :: [Name] -> Name -> Val -> Val -> System Val -> Val
compNeg is i a u ts = comp is i (sym is a i) u (sym is ts i)

compLine :: [Name] -> Val -> Val -> System Val -> Val
compLine is a u ts =
  comp is' i (appFormula is' a i) u (Map.map (\t -> appFormula is' t i) ts)
    where i = fresh (a,u,ts) -- gensym is
          is' = i:is

compConstLine :: [Name] -> Val -> Val -> System Val -> Val
compConstLine is a u ts =
  comp is' i a u (Map.map (\t -> appFormula is' t i) ts)
    where i = fresh (a,u,ts) -- gensym is
          is' = i:is

comps :: [Name] -> Name -> [(Ident,Ter)] -> Env -> [(System Val,Val)] -> [Val]
comps _ _ []         _ []         = []
comps is i ((x,a):as) e ((ts,u):tsus) =
  let v   = fill is i (eval is e a) u ts
      vi1 = comp is i (eval is e a) u ts
      vs  = comps is i as (upd (x,v) e) tsus
  in vi1 : vs
comps _ _ _ _ _ = error "comps: different lengths of types and values"

fill :: [Name] -> Name -> Val -> Val -> System Val -> Val
fill is i a u ts =
  comp is' j (conj is' a (i,j)) u (insertSystem (i ~> 0) u (conj is' ts (i,j)))
  where j = fresh (Atom i,a,u,ts) -- gensym (i:is)
        is' = j:is   -- Anders: add i?

fillNeg :: [Name] -> Name -> Val -> Val -> System Val -> Val
fillNeg is i a u ts = sym is (fill is i (sym is a i) u (sym is ts i)) i

fillLine :: [Name] -> Val -> Val -> System Val -> Val
fillLine is a u ts =
  VPLam i $ fill is' i (appFormula is' a i) u (Map.map (\t -> appFormula is' t i) ts)
    where i = fresh (a,u,ts) -- gensym is
          is' = i:is

-- fills :: Name -> [(Ident,Ter)] -> Env -> [(System Val,Val)] -> [Val]
-- fills i []         _ []         = []
-- fills i ((x,a):as) e ((ts,u):tsus) =
--   let v  = fill i (eval e a) ts u
--       vs = fills i as (Upd e (x,v)) tsus
--   in v : vs
-- fills _ _ _ _ = error "fills: different lengths of types and values"


-----------------------------------------------------------
-- Transport and squeeze (defined using comp)

trans :: [Name] -> Name -> Val -> Val -> Val
trans is i v0 v1 = comp is i v0 v1 empty

transNeg :: [Name] -> Name -> Val -> Val -> Val
transNeg is i a u = trans is i (sym is a i) u

transLine :: [Name] -> Val -> Val -> Val
transLine is u v = trans is' i (appFormula is' u i) v
  where i = fresh (u,v) -- gensym is
        is' = i:is

transNegLine :: [Name] -> Val -> Val -> Val
transNegLine is u v = transNeg is' i (appFormula is' u i) v
  where i = fresh (u,v) -- gensym is
        is' = i:is

-- TODO: define in terms of comps?
transps :: [Name] -> Name -> [(Ident,Ter)] -> Env -> [Val] -> [Val]
transps is _ []         _ []     = []
transps is i ((x,a):as) e (u:us) =
  let v   = transFill is i (eval is e a) u
      vi1 = trans is i (eval is e a) u
      vs  = transps is i as (upd (x,v) e) us
  in vi1 : vs
transps _ _ _ _ _ = error "transps: different lengths of types and values"

transFill :: [Name] -> Name -> Val -> Val -> Val
transFill is i a u = fill is i a u empty

transFillNeg :: [Name] -> Name -> Val -> Val -> Val
transFillNeg is i a u = sym is (transFill is i (sym is a i) u) i

-- Given u of type a "squeeze i a u" connects in the direction i
-- trans i a u(i=0) to u(i=1)
squeeze :: [Name] -> Name -> Val -> Val -> Val
squeeze is i a u = comp is' j (disj is' a (i,j)) u $ mkSystem [ (i ~> 1, ui1) ]
  where j   = fresh (Atom i,a,u) -- gensym (i:is)
        is' = j:is -- TODO: comp with (i:j:is)?
        ui1 = face is' u (i ~> 1)

squeezes :: [Name] -> Name -> [(Ident,Ter)] -> Env -> [Val] -> [Val]
squeezes is i xas e us = comps is' j xas (disj is' e (i,j)) us'
  where j   = fresh (Atom i,e,us) -- gensym (i:is) -- Anders: same as in squeeze?
        is' = j:is
        us' = [ (mkSystem [(i ~> 1, face is' u (i ~> 1))],u) | u <- us ]


-------------------------------------------------------------------------------
-- | HITs

pcon :: [Name] -> LIdent -> Val -> [Val] -> [Formula] -> Val
pcon is c a@(Ter (HSum _ _ lbls) rho) us phis = case lookupPLabel c lbls of
  Just (tele,is',ts) | eps `member` vs -> vs ! eps
                     | otherwise       -> VPCon c a us phis
    where rho' = subs (zip is' phis) (updsTele tele us rho)
          vs   = evalSystem is rho' ts -- Anders: add is'?
  Nothing           -> error "pcon"
pcon is c a us phi     = VPCon c a us phi

compHIT :: [Name] -> Name -> Val -> Val -> System Val -> Val
compHIT is i a u us
  | isNeutral u || isNeutralSystem us =
      VComp (VPLam i a) u (Map.map (VPLam i) us)
  | otherwise =
      hComp is (face is a (i ~> 1)) (transpHIT is i a u) $
        mapWithKey (\alpha uAlpha ->
                     VPLam i $ squeezeHIT (i:is) i (face (i:is) a alpha) uAlpha) us

-- Given u of type a(i=0), transpHIT i a u is an element of a(i=1).
transpHIT :: [Name] -> Name -> Val -> Val -> Val
transpHIT is i a@(Ter (HSum _ _ nass) env) u =
 let j = fresh (a,u) -- gensym is
     is' = j:is -- TODO: add i?
     aij = swap a (i,j)
 in
 case u of
  VCon n us -> case lookupLabel n nass of
    Just as -> VCon n (transps is' i as env us)
    Nothing -> error $ "transpHIT: missing constructor in labelled sum " ++ n
  VPCon c _ ws0 phis -> case lookupLabel c nass of
    Just as -> pcon is' c (face is' a (i ~> 1)) (transps is' i as env ws0) phis
    Nothing -> error $ "transpHIT: missing path constructor " ++ c
  VHComp _ v vs ->
    hComp is' (face is' a (i ~> 1)) (transpHIT is' i a v) $
      mapWithKey (\alpha vAlpha ->
                   VPLam j $ transpHIT is' j (face is' aij alpha) (appFormula is' vAlpha j)) vs
  _ -> error $ "transpHIT: neutral " ++ show u

-- given u(i) of type a(i) "squeezeHIT i a u" connects in the direction i
-- transHIT i a u(i=0) to u(i=1) in a(1)
squeezeHIT :: [Name] -> Name -> Val -> Val -> Val
squeezeHIT is i a@(Ter (HSum _ _ nass) env) u =
 let j = fresh (a,u) -- gensym is
     is' = j:is -- TODO: add i?
 in
 case u of
  VCon n us -> case lookupLabel n nass of
    Just as -> VCon n (squeezes is' i as env us)
    Nothing -> error $ "squeezeHIT: missing constructor in labelled sum " ++ n
  VPCon c _ ws0 phis -> case lookupLabel c nass of
    Just as -> pcon is' c (face is' a (i ~> 1)) (squeezes is' i as env ws0) phis
    Nothing -> error $ "squeezeHIT: missing path constructor " ++ c
  VHComp _ v vs -> hComp is' (face is' a (i ~> 1)) (squeezeHIT is' i a v) $
      mapWithKey
        (\alpha vAlpha -> case Map.lookup i alpha of
          Nothing   -> VPLam j $ squeezeHIT is' i (face is' a alpha) (appFormula is' vAlpha j)
          Just Zero -> VPLam j $ transpHIT is' i
                         (face is' a (Map.delete i alpha)) (appFormula is' vAlpha j)
          Just One  -> vAlpha)
        vs
  _ -> error $ "squeezeHIT: neutral " ++ show u

hComp :: [Name] -> Val -> Val -> System Val -> Val
hComp is a u us | eps `member` us = appFormula is (us ! eps) One
                | otherwise       = VHComp a u us

-------------------------------------------------------------------------------
-- | Glue

-- An equivalence for a type a is a triple (t,f,p) where
-- t : U
-- f : t -> a
-- p : (x : a) -> isContr ((y:t) * Id a x (f y))
-- with isContr c = (z : c) * ((z' : C) -> Id c z z')

-- Extraction functions for getting a, f, s and t:
equivDom :: Val -> Val
equivDom = fstVal

equivFun :: Val -> Val
equivFun = fstVal . sndVal

equivContr :: Val -> Val
equivContr =  sndVal . sndVal

glue :: Val -> System Val -> Val
glue b ts | eps `member` ts = equivDom (ts ! eps)
          | otherwise       = VGlue b ts

glueElem :: Val -> System Val -> Val
glueElem (VUnGlueElem u _) _ = u
glueElem v us | eps `member` us = us ! eps
              | otherwise       = VGlueElem v us

unglueElem :: [Name] -> Val -> System Val -> Val
unglueElem is w isos | eps `member` isos = app is (equivFun (isos ! eps)) w
                     | otherwise         = case w of
                                          VGlueElem v us -> v
                                          _ -> VUnGlueElem w isos

unGlue :: [Name] -> Val -> Val -> System Val -> Val
unGlue is w b equivs | eps `member` equivs = app is (equivFun (equivs ! eps)) w
                     | otherwise           = case w of
                                            VGlueElem v us -> v
                                            _ -> error ("unglue: neutral" ++ show w)

isNeutralGlue :: [Name] -> Name -> System Val -> Val -> System Val -> Bool
isNeutralGlue is i equivs u0 ts = (eps `notMember` equivsi0 && isNeutral u0) ||
  any (\(alpha,talpha) ->
           eps `notMember` (face is' equivs alpha) && isNeutral talpha)
    (assocs ts)
  where equivsi0 = face is' equivs (i ~> 0)
        is' = i:is

-- this is exactly the same as isNeutralGlue?
isNeutralU :: [Name] -> Name -> System Val -> Val -> System Val -> Bool
isNeutralU is i eqs u0 ts = (eps `notMember` eqsi0 && isNeutral u0) ||
  any (\(alpha,talpha) ->
           eps `notMember` (face is' eqs alpha) && isNeutral talpha)
    (assocs ts)
  where eqsi0 = face is' eqs (i ~> 0)
        is' = i:is

-- Extend the system ts to a total element in b given q : isContr b
extend :: [Name] -> Val -> Val -> System Val -> Val
extend is b q ts = comp is' i b (fstVal q) ts'
  where i = fresh (b,q,ts) -- TODO: fix
        is' = i:is
        ts' = mapWithKey
                (\alpha tAlpha ->
                  appFormula is' (app is' (face is' (sndVal q) alpha) tAlpha) i) ts

-- psi/b corresponds to ws
-- b0    corresponds to wi0
-- a0    corresponds to vi0
-- psi/a corresponds to vs
-- a1'   corresponds to vi1'
-- equivs' corresponds to delta
-- ti1'  corresponds to usi1'
compGlue :: [Name] -> Name -> Val -> System Val -> Val -> System Val -> Val
compGlue is i a equivs wi0 ws = glueElem vi1 usi1
  where ai1 = face is a (i ~> 1)
        vs  = mapWithKey
                (\alpha wAlpha ->
                  unGlue is wAlpha (face is a alpha) (face is equivs alpha)) ws

        vsi1 = face is vs (i ~> 1) -- same as: border vi1 vs
        vi0  = unGlue is wi0 (face is a (i ~> 0)) (face is equivs (i ~> 0)) -- in a(i0)

        vi1'  = comp is i a vi0 vs           -- in a(i1)

        equivsI1 = face is equivs (i ~> 1)
        equivs'  = filterWithKey (\alpha _ -> i `notMember` alpha) equivs

        us'    = mapWithKey (\gamma equivG ->
                   fill is i (equivDom equivG) (face is wi0 gamma) (face is ws gamma))
                 equivs'
        usi1'  = mapWithKey (\gamma equivG ->
                   comp is i (equivDom equivG) (face is wi0 gamma) (face is ws gamma))
                 equivs'

        -- path in ai1 between vi1 and f(i1) usi1' on equivs'
        ls'    = mapWithKey (\gamma equivG ->
                   pathComp is i (face is a gamma) (face is vi0 gamma)
                     (app is (equivFun equivG) (us' ! gamma)) (face is vs gamma))
                 equivs'

        fibersys = intersectionWith VPair usi1' ls' -- on equivs'

        wsi1 = face is ws (i ~> 1)
        fibersys' = mapWithKey
          (\gamma equivG ->
            let fibsgamma = intersectionWith (\ x y -> VPair x (constPath y))
                              (face is wsi1 gamma) (face is vsi1 gamma)
            in extend is (mkFiberType is (face is ai1 gamma) (face is vi1' gamma) equivG)
                 (app is (equivContr equivG) (face is vi1' gamma))
                 (fibsgamma `unionSystem` (face is fibersys gamma))) equivsI1

        vi1 = compConstLine is ai1 vi1'
                (Map.map sndVal fibersys' `unionSystem` Map.map constPath vsi1)

        usi1 = Map.map fstVal fibersys'

mkFiberType :: [Name] -> Val -> Val -> Val -> Val
mkFiberType is a x equiv = eval is rho $
  Sigma $ Lam "y" tt (PathP (PLam (Name "_") ta) tx (App tf ty))
  where [ta,tx,ty,tf,tt] = map Var ["a","x","y","f","t"]
        rho = upds [("a",a),("x",x),("f",equivFun equiv)
                   ,("t",equivDom equiv)] emptyEnv

-- Assumes u' : A is a solution of us + (i0 -> u0)
-- The output is an L-path in A(i1) between comp i u0 us and u'(i1)
pathComp :: [Name] -> Name -> Val -> Val -> Val -> System Val -> Val
pathComp is i a u0 u' us = VPLam j $ comp is' i a u0 us'
  where j   = fresh (Atom i,a,us,u0,u') -- gensym is
        is' = j:is
        us' = insertsSystem [(j ~> 1, u')] us

-------------------------------------------------------------------------------
-- | Composition in the Universe

-- any path between types define an equivalence
eqFun :: [Name] -> Val -> Val -> Val
eqFun = transNegLine

unGlueU :: [Name] -> Val -> Val -> System Val -> Val
unGlueU is w b es | eps `Map.member` es = eqFun is (es ! eps) w
                  | otherwise           = case w of
                                        VGlueElem v us   -> v
                                        _ -> VUnGlueElemU w b es

compUniv :: [Name] -> Val -> System Val -> Val
compUniv is b es | eps `Map.member` es = appFormula is (es ! eps) One
                 | otherwise           = VCompU b es

compU :: [Name] -> Name -> Val -> System Val -> Val -> System Val -> Val
compU is i a eqs wi0 ws = glueElem vi1 usi1
  where ai1 = face is a (i ~> 1)
        vs  = mapWithKey
                (\alpha wAlpha ->
                  unGlueU is wAlpha (face is a alpha) (face is eqs alpha)) ws

        vsi1 = face is vs (i ~> 1) -- same as: border vi1 vs
        vi0  = unGlueU is wi0 (face is a (i ~> 0)) (face is eqs (i ~> 0)) -- in a(i0)

        vi1'  = comp is i a vi0 vs           -- in a(i1)

        eqsI1 = face is eqs (i ~> 1)
        eqs'  = filterWithKey (\alpha _ -> i `notMember` alpha) eqs

        us'    = mapWithKey (\gamma eqG ->
                   fill is i (appFormula is eqG One) (face is wi0 gamma) (face is ws gamma))
                 eqs'
        usi1'  = mapWithKey (\gamma eqG ->
                   comp is i (appFormula is eqG One) (face is wi0 gamma) (face is ws gamma))
                 eqs'

        -- path in ai1 between vi1 and f(i1) usi1' on eqs'
        ls'    = mapWithKey (\gamma eqG ->
                   pathComp is i (face is a gamma) (face is vi0 gamma)
                     (eqFun is eqG (us' ! gamma)) (face is vs gamma))
                 eqs'

        fibersys = intersectionWith (\ x y -> (x,y)) usi1' ls' -- on eqs'

        wsi1 = face is ws (i ~> 1)
        fibersys' = mapWithKey
          (\gamma eqG ->
            let fibsgamma = intersectionWith (\ x y -> (x,constPath y))
                              (face is wsi1 gamma) (face is vsi1 gamma)
            in lemEq is eqG (face is vi1' gamma)
                     (fibsgamma `unionSystem` (face is fibersys gamma))) eqsI1

        vi1 = compConstLine is ai1 vi1'
                (Map.map snd fibersys' `unionSystem` Map.map constPath vsi1)

        usi1 = Map.map fst fibersys'

lemEq :: [Name] -> Val -> Val -> System (Val,Val) -> (Val,Val)
lemEq is eq b aps = (a,VPLam i (compNeg is' j (appFormula is' eq j) p1 thetas'))
 where
   i:j:_ = freshs (eq,b,aps) -- gensym is
   is'   = i:j:is
   ta = appFormula is' eq One
   p1s = mapWithKey (\alpha (aa,pa) ->
              let eqaj = appFormula is' (face is' eq alpha) j
                  ba = face is' b alpha
              in comp is' j eqaj (appFormula is' pa i)
                   (mkSystem [ (i~>0,transFill is' j eqaj ba)
                             , (i~>1,transFillNeg is' j eqaj aa)])) aps
   thetas = mapWithKey (\alpha (aa,pa) ->
              let eqaj = appFormula is' (face is' eq alpha) j
                  ba = face is' b alpha
              in fill is' j eqaj (appFormula is' pa i)
                   (mkSystem [ (i~>0,transFill is' j eqaj ba)
                             , (i~>1,transFillNeg is' j eqaj aa)])) aps

   a  = comp is' i ta (trans is' i (appFormula is' eq i) b) p1s
   p1 = fill is' i ta (trans is' i (appFormula is' eq i) b) p1s

   thetas' = insertsSystem [ (i ~> 0,transFill is' j (appFormula is' eq j) b)
                           , (i ~> 1,transFillNeg is' j (appFormula is' eq j) a)] thetas

-- Old version:
-- This version triggers the following error when checking the normal form of corrUniv:
-- Parsed "examples/nunivalence2.ctt" successfully!
-- Resolver failed: Cannot resolve name !3 at position (7,30062) in module nunivalence2
-- compU :: Name -> Val -> System Val -> Val -> System Val -> Val
-- compU i b es wi0 ws = glueElem vi1'' usi1''
--   where bi1 = b `face` (i ~> 1)
--         vs   = mapWithKey (\alpha wAlpha ->
--                  unGlueU wAlpha (b `face` alpha) (es `face` alpha)) ws
--         vsi1 = vs `face` (i ~> 1) -- same as: border vi1 vs
--         vi0  = unGlueU wi0 (b `face` (i ~> 0)) (es `face` (i ~> 0)) -- in b(i0)

--         v    = fill i b vi0 vs           -- in b
--         vi1  = comp i b vi0 vs           -- is v `face` (i ~> 1) in b(i1)

--         esI1 = es `face` (i ~> 1)
--         es'  = filterWithKey (\alpha _ -> i `Map.notMember` alpha) es
--         es'' = filterWithKey (\alpha _ -> alpha `Map.notMember` es) esI1

--         us'    = mapWithKey (\gamma eGamma ->
--                    fill i (eGamma @@ One) (wi0 `face` gamma) (ws `face` gamma))
--                  es'
--         usi1'  = mapWithKey (\gamma eGamma ->
--                    comp i (eGamma @@ One) (wi0 `face` gamma) (ws `face` gamma))
--                  es'

--         ls'    = mapWithKey (\gamma eGamma ->
--                      pathComp i (b `face` gamma) (v `face` gamma)
--                        (transNegLine eGamma (us' ! gamma)) (vs `face` gamma))
--                    es'

--         vi1' = compLine (constPath bi1) vi1
--                  (ls' `unionSystem` Map.map constPath vsi1)

--         wsi1 = ws `face` (i ~> 1)

--         -- for gamma in es'', (i1) gamma is in es, so wsi1 gamma
--         -- is in the domain of isoGamma
--         uls'' = mapWithKey (\gamma eGamma ->
--                   gradLemmaU (bi1 `face` gamma) eGamma
--                     ((usi1' `face` gamma) `unionSystem` (wsi1 `face` gamma))
--                     (vi1' `face` gamma))
--                   es''

--         vsi1' = Map.map constPath $ border vi1' es' `unionSystem` vsi1

--         vi1'' = compLine (constPath bi1) vi1'
--                   (Map.map snd uls'' `unionSystem` vsi1')

--         usi1'' = Map.mapWithKey (\gamma _ ->
--                      if gamma `Map.member` usi1' then usi1' ! gamma
--                      else fst (uls'' ! gamma))
--                   esI1

-- Grad Lemma, takes a line eq in U, a system us and a value v, s.t. f us =
-- border v. Outputs (u,p) s.t. border u = us and a path p between v
-- and f u, where f is transNegLine eq
-- gradLemmaU :: Val -> Val -> System Val -> Val -> (Val, Val)
-- gradLemmaU b eq us v = (u, VPLam i theta)
--   where i:j:_   = freshs (b,eq,us,v)
--         ej      = eq @@ j
--         a       = eq @@ One
--         ws      = mapWithKey (\alpha uAlpha ->
--                                    transFillNeg j (ej `face` alpha) uAlpha) us
--         u       = comp j ej v ws
--         w       = fill j ej v ws
--         xs      = insertSystem (i ~> 0) w $
--                   insertSystem (i ~> 1) (transFillNeg j ej u) $ ws
--         theta   = compNeg j ej u xs

-- Old version:
-- gradLemmaU :: Val -> Val -> System Val -> Val -> (Val, Val)
-- gradLemmaU b eq us v = (u, VPLam i theta'')
--   where i:j:_   = freshs (b,eq,us,v)
--         a       = eq @@ One
--         g       = transLine
--         f       = transNegLine
--         s e y   = VPLam j $ compNeg i (e @@ i) (trans i (e @@ i) y)
--                     (mkSystem [(j ~> 0, transFill j (e @@ j) y)
--                               ,(j ~> 1, transFillNeg j (e @@ j)
--                                           (trans j (e @@ j) y))])
--         t e x   = VPLam j $ comp i (e @@ i) (transNeg i (e @@ i) x)
--                     (mkSystem [(j ~> 0, transFill j (e @@ j)
--                                           (transNeg j (e @@ j) x))
--                               ,(j ~> 1, transFillNeg j (e @@ j) x)])
--         gv      = g eq v
--         us'     = mapWithKey (\alpha uAlpha ->
--                                    t (eq `face` alpha) uAlpha @@ i) us
--         theta   = fill i a gv us'
--         u       = comp i a gv us'  -- Same as "theta `face` (i ~> 1)"
--         ws      = insertSystem (i ~> 0) gv $
--                   insertSystem (i ~> 1) (t eq u @@ j) $
--                   mapWithKey
--                     (\alpha uAlpha ->
--                       t (eq `face` alpha) uAlpha @@ (Atom i :/\: Atom j)) us
--         theta'  = compNeg j a theta ws
--         xs      = insertSystem (i ~> 0) (s eq v @@ j) $
--                   insertSystem (i ~> 1) (s eq (f eq u) @@ j) $
--                   mapWithKey
--                     (\alpha uAlpha ->
--                        s (eq `face` alpha) (f (eq `face` alpha) uAlpha) @@ j) us
--         theta'' = comp j b (f eq theta') xs


-------------------------------------------------------------------------------
-- | Conversion

class Convertible a where
  conv :: [Name] -> [String] -> a -> a -> Bool

isCompSystem :: (Nominal a, Convertible a) => [Name] -> [String] -> System a -> Bool
isCompSystem is ns ts =
  and [ conv is ns (getFace alpha beta) (getFace beta alpha)
      | (alpha,beta) <- allCompatible (keys ts) ]
    where getFace a b = face is (ts ! a) (b `minus` a)

instance Convertible Val where
  conv is ns u v | u == v = True
              | otherwise =
    let j = fresh (u,v) -- todo: fix
    in case (u,v) of
      (Ter (Lam x a u) e,Ter (Lam x' a' u') e') ->
        let v@(VVar n _) = mkVarNice ns x (eval is e a)
        in conv is (n:ns) (eval is (upd (x,v) e) u) (eval is (upd (x',v) e') u')
      (Ter (Lam x a u) e,u') ->
        let v@(VVar n _) = mkVarNice ns x (eval is e a)
        in conv is (n:ns) (eval is (upd (x,v) e) u) (app is u' v)
      (u',Ter (Lam x a u) e) ->
        let v@(VVar n _) = mkVarNice ns x (eval is e a)
        in conv is (n:ns) (app is u' v) (eval is (upd (x,v) e) u)
      (Ter (Split _ p _ _) e,Ter (Split _ p' _ _) e') -> (p == p') && conv is ns e e'
      (Ter (Sum p _ _) e,Ter (Sum p' _ _) e')         -> (p == p') && conv is ns e e'
      (Ter (HSum p _ _) e,Ter (HSum p' _ _) e')       -> (p == p') && conv is ns e e'
      (Ter (Undef p _) e,Ter (Undef p' _) e') -> p == p' && conv is ns e e'
      (Ter (Hole p) e,Ter (Hole p') e') -> p == p' && conv is ns e e'
      -- (Ter Hole{} e,_) -> True
      -- (_,Ter Hole{} e') -> True
      (VPi u v,VPi u' v') ->
        let w@(VVar n _) = mkVarNice ns "X" u
        in conv is ns u u' && conv is (n:ns) (app is v w) (app is v' w)
      (VSigma u v,VSigma u' v') ->
        let w@(VVar n _) = mkVarNice ns "X" u
        in conv is ns u u' && conv is (n:ns) (app is v w) (app is v' w)
      (VCon c us,VCon c' us')   -> (c == c') && conv is ns us us'
      (VPCon c v us phis,VPCon c' v' us' phis') ->
        (c == c') && conv is ns (v,us,phis) (v',us',phis')
      (VPair u v,VPair u' v')    -> conv is ns (u,v) (u',v')
      (VPair u v,w)              -> conv is ns u (fstVal w) && conv is ns v (sndVal w)
      (w,VPair u v)              -> conv is ns (fstVal w) u && conv is ns (sndVal w) v
      (VFst u,VFst u')           -> conv is ns u u'
      (VSnd u,VSnd u')           -> conv is ns u u'
      (VApp u v,VApp u' v')      -> conv is ns (u,v) (u',v')
      (VSplit u v,VSplit u' v')  -> conv is ns (u,v) (u',v')
      (VOpaque x _, VOpaque x' _) -> x == x'
      (VVar x _, VVar x' _)       -> x == x'
      (VPathP a b c,VPathP a' b' c') -> conv is ns (a,b,c) (a',b',c')
      (VPLam i a,VPLam i' a')    -> conv (j:is) ns (a `swap` (i,j)) (a' `swap` (i',j))
      (VPLam i a,p')             -> conv (j:is) ns (a `swap` (i,j)) (appFormula (j:is) p' j)
      (p,VPLam i' a')            -> conv (j:is) ns (appFormula (j:is) p j) (a' `swap` (i',j))
      (VAppFormula u x,VAppFormula u' x') -> conv is ns (u,x) (u',x')
      (VComp a u ts,VComp a' u' ts')      -> conv is ns (a,u,ts) (a',u',ts')
      (VHComp a u ts,VHComp a' u' ts')    -> conv is ns (a,u,ts) (a',u',ts')
      (VGlue v equivs,VGlue v' equivs')   -> conv is ns (v,equivs) (v',equivs')
      (VGlueElem u us,VGlueElem u' us')   -> conv is ns (u,us) (u',us')
      (VUnGlueElemU u _ _,VUnGlueElemU u' _ _) -> conv is ns u u'
      (VUnGlueElem u ts,VUnGlueElem u' ts')    -> conv is ns (u,ts) (u',ts')
      (VCompU u es,VCompU u' es')              -> conv is ns (u,es) (u',es')
      _                                        -> False

instance Convertible Ctxt where
  conv _ _ _ _ = True

instance Convertible () where
  conv _ _ _ _ = True

instance (Convertible a, Convertible b) => Convertible (a, b) where
  conv is ns (u, v) (u', v') = conv is ns u u' && conv is ns v v'

instance (Convertible a, Convertible b, Convertible c)
      => Convertible (a, b, c) where
  conv is ns (u, v, w) (u', v', w') = conv is ns (u,(v,w)) (u',(v',w'))

instance (Convertible a,Convertible b,Convertible c,Convertible d)
      => Convertible (a,b,c,d) where
  conv is ns (u,v,w,x) (u',v',w',x') = conv is ns (u,v,(w,x)) (u',v',(w',x'))

instance Convertible a => Convertible [a] where
  conv is ns us us' = length us == length us' &&
                      and [conv is ns u u' | (u,u') <- zip us us']

instance Convertible a => Convertible (System a) where
  conv is ns ts ts' = keys ts == keys ts' &&
                      and (elems (intersectionWith (conv is ns) ts ts'))

instance Convertible Formula where
  conv _ _ phi psi = dnf phi == dnf psi

instance Convertible (Nameless a) where
  conv _ _ _ _ = True

-------------------------------------------------------------------------------
-- | Normalization

class Normal a where
  normal :: [Name] -> [String] -> a -> a

instance Normal Val where
  normal is ns v = case v of
    VU                  -> VU
    Ter (Lam x t u) e   ->
      let w = eval is e t
          v@(VVar n _) = mkVarNice ns x w
      in VLam n (normal is ns w) $ normal is (n:ns) (eval is (upd (x,v) e) u)
    Ter t e             -> Ter t (normal is ns e)
    VPi u v             -> VPi (normal is ns u) (normal is ns v)
    VSigma u v          -> VSigma (normal is ns u) (normal is ns v)
    VPair u v           -> VPair (normal is ns u) (normal is ns v)
    VCon n us           -> VCon n (normal is ns us)
    VPCon n u us phis   -> VPCon n (normal is ns u) (normal is ns us) phis
    VPathP a u0 u1      -> VPathP (normal is ns a) (normal is ns u0) (normal is ns u1)
    VPLam i u           -> VPLam i (normal (i:is) ns u)
    VComp u v vs        -> compLine is (normal is ns u) (normal is ns v) (normal is ns vs)
    VHComp u v vs       -> hComp is (normal is ns u) (normal is ns v) (normal is ns vs)
    VGlue u equivs      -> glue (normal is ns u) (normal is ns equivs)
    VGlueElem u us      -> glueElem (normal is ns u) (normal is ns us)
    VUnGlueElem u us    -> unglueElem is (normal is ns u) (normal is ns us)
    VUnGlueElemU e u us -> unGlueU is (normal is ns e) (normal is ns u) (normal is ns us)
    VCompU a ts         -> VCompU (normal is ns a) (normal is ns ts)
    VVar x t            -> VVar x t -- (normal is ns t)
    VFst t              -> fstVal (normal is ns t)
    VSnd t              -> sndVal (normal is ns t)
    VSplit u t          -> VSplit (normal is ns u) (normal is ns t)
    VApp u v            -> app is (normal is ns u) (normal is ns v)
    VAppFormula u phi   -> VAppFormula (normal is ns u) (normal is ns phi)
    _                   -> v

instance Normal (Nameless a) where
  normal _ _ = id

instance Normal Ctxt where
  normal _ _ = id

instance Normal Formula where
  normal _ _ = fromDNF . dnf

instance Normal a => Normal (Map k a) where
  normal is ns = Map.map (normal is ns)

instance (Normal a,Normal b) => Normal (a,b) where
  normal is ns (u,v) = (normal is ns u,normal is ns v)

instance (Normal a,Normal b,Normal c) => Normal (a,b,c) where
  normal is ns (u,v,w) = (normal is ns u,normal is ns v,normal is ns w)

instance (Normal a,Normal b,Normal c,Normal d) => Normal (a,b,c,d) where
  normal is ns (u,v,w,x) =
    (normal is ns u,normal is ns v,normal is ns w, normal is ns x)

instance Normal a => Normal [a] where
  normal is ns = map (normal is ns)
