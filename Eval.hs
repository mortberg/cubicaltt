{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Eval where

import Data.List
import Data.Maybe (fromMaybe)
import Data.Map (Map,(!),mapWithKey,assocs,filterWithKey
                ,elems,intersectionWith,intersection,keys
                ,member,notMember,empty)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Connections
import CTT



-----------------------------------------------------------------------
-- Lookup functions

look :: String -> Env -> Val
look x (Env (Upd y rho,v:vs,fs,os)) | x == y = v
                                    | otherwise = look x (Env (rho,vs,fs,os))
look x r@(Env (Def _ decls rho,vs,fs,Nameless os)) = case lookup x decls of
  Just (_,t) -> eval r t
  Nothing    -> look x (Env (rho,vs,fs,Nameless os))
look x (Env (Sub _ rho,vs,_:fs,os)) = look x (Env (rho,vs,fs,os))
look x (Env (Empty,_,_,_)) = error $ "look: not found " ++ show x

lookType :: String -> Env -> Val
lookType x (Env (Upd y rho,v:vs,fs,os))
  | x /= y        = lookType x (Env (rho,vs,fs,os))
  | VVar _ a <- v = a
  | otherwise     = error ""
lookType x r@(Env (Def _ decls rho,vs,fs,os)) = case lookup x decls of
  Just (a,_) -> eval r a
  Nothing -> lookType x (Env (rho,vs,fs,os))
lookType x (Env (Sub _ rho,vs,_:fs,os)) = lookType x (Env (rho,vs,fs,os))
lookType x (Env (Empty,_,_,_))          = error $ "lookType: not found " ++ show x

lookName :: Name -> Env -> Formula
lookName i (Env (Upd _ rho,v:vs,fs,os)) = lookName i (Env (rho,vs,fs,os))
lookName i (Env (Def _ _ rho,vs,fs,os)) = lookName i (Env (rho,vs,fs,os))
lookName i (Env (Sub j rho,vs,phi:fs,os)) | i == j    = phi
                                          | otherwise = lookName i (Env (rho,vs,fs,os))
lookName i _ = error $ "lookName: not found " ++ show i


-----------------------------------------------------------------------
-- Nominal instances

instance Nominal Ctxt where
--  support _ = []
  occurs _ _ = False
  act b e _   = e
  swap e _  = e

instance Nominal Env where
--  support (Env (rho,vs,fs,os)) = support (rho,vs,fs,os)
  occurs x (Env (rho,vs,fs,os)) = occurs x (rho,vs,fs,os)
  -- Strangely this definition seems to lead to a space leak:
  -- act b (Env (rho,vs,fs,os)) iphi = Env $ act b (rho,vs,fs,os) iphi
  act b (Env (rho,vs,fs,os)) iphi = Env (rho,act b vs iphi,act b fs iphi,os)
  swap (Env (rho,vs,fs,os)) ij = Env (rho,swap vs ij,swap fs ij, os)

instance Nominal Val where
  -- support v = case v of
  --   VU                      -> []
  --   Ter _ e                 -> support e
  --   VPi u v                 -> support [u,v]
  --   VPathP a v0 v1          -> support [a,v0,v1]
  --   VPLam i v               -> i `delete` support v
  --   VSigma u v              -> support (u,v)
  --   VPair u v               -> support (u,v)
  --   VFst u                  -> support u
  --   VSnd u                  -> support u
  --   VCon _ vs               -> support vs
  --   VPCon _ a vs phis       -> support (a,vs,phis)
  --   VHComp a u ts           -> support (a,u,ts)
  --   VTrans a phi u          -> support (a,phi,u)
  --   VVar _ v                -> support v
  --   VOpaque _ v             -> support v
  --   VApp u v                -> support (u,v)
  --   VLam _ u v              -> support (u,v)
  --   VAppFormula u phi       -> support (u,phi)
  --   VSplit u v              -> support (u,v)
  --   VGlue a ts              -> support (a,ts)
  --   VGlueElem a ts          -> support (a,ts)
  --   VUnGlueElem a b ts      -> support (a,b,ts)
  --   VHCompU a ts            -> support (a,ts)
  --   VUnGlueElemU a b es     -> support (a,b,es)
  --   VIdPair u us            -> support (u,us)
  --   VId a u v               -> support (a,u,v)
  --   VIdJ a u c d x p        -> support [a,u,c,d,x,p]
  occurs x v = case v of
    VU                      -> False
    Ter _ e                 -> occurs x e
    VPi u v                 -> occurs x (u,v)
    VPathP a v0 v1          -> occurs x [a,v0,v1]
    VPLam i v               -> if x == i then False else occurs x v
    VSigma u v              -> occurs x (u,v)
    VPair u v               -> occurs x (u,v)
    VFst u                  -> occurs x u
    VSnd u                  -> occurs x u
    VCon _ vs               -> occurs x vs
    VPCon _ a vs phis       -> occurs x (a,vs,phis)
    VHComp a u ts           -> occurs x (a,u,ts)
    VTrans a phi u          -> occurs x (a,phi,u)
    VVar _ v                -> occurs x v
    VOpaque _ v             -> occurs x v
    VApp u v                -> occurs x (u,v)
    VLam _ u v              -> occurs x (u,v)
    VAppFormula u phi       -> occurs x (u,phi)
    VSplit u v              -> occurs x (u,v)
    VGlue a ts              -> occurs x (a,ts)
    VGlueElem a ts          -> occurs x (a,ts)
    VUnGlueElem a b ts      -> occurs x (a,b,ts)
    VHCompU a ts            -> occurs x (a,ts)
    VUnGlueElemU a b es     -> occurs x (a,b,es)
    VIdPair u us            -> occurs x (u,us)
    VId a u v               -> occurs x (a,u,v)
    VIdJ a u c d y p        -> occurs x [a,u,c,d,y,p]

  act b u (i, phi)
    | b = case u of
         VU           -> VU
         Ter t e      -> Ter t (act b e (i,phi))
         VPi a f      -> VPi (act b a (i,phi)) (act b f (i,phi))
         VPathP a u v -> VPathP (act b a (i,phi)) (act b u (i,phi)) (act b v (i,phi))
         VPLam j v | j == i -> u
                   | not (j `occurs` phi) -> VPLam j (act b v (i,phi))
                   | otherwise -> VPLam k (act b (v `swap` (j,k)) (i,phi))
              where k = fresh (v,Atom i,phi)
         VSigma a f              -> VSigma (act b a (i,phi)) (act b f (i,phi))
         VPair u v               -> VPair (act b u (i,phi)) (act b v (i,phi))
         VFst u                  -> fstVal (act b u (i,phi))
         VSnd u                  -> sndVal (act b u (i,phi))
         VCon c vs               -> VCon c (act b vs (i,phi))
         VPCon c a vs phis       -> pcon c (act b a (i,phi)) (act b vs (i,phi)) (act b phis (i,phi))
         VHComp a u us           -> hcompLine (act b a (i,phi)) (act b u (i,phi)) (act b us (i,phi))
         VTrans a psi u          -> transLine (act b a (i,phi)) (act b psi (i,phi)) (act b u (i,phi))
         VVar x v                -> VVar x (act b v (i,phi))
         VOpaque x v             -> VOpaque x (act b v (i,phi))
         VAppFormula u psi       -> act b u (i,phi) @@ act b psi (i,phi)
         VApp u v                -> app (act b u (i,phi)) (act b v (i,phi))
         VLam x t u              -> VLam x (act b t (i,phi)) (act b u (i,phi))
         VSplit u v              -> app (act b u (i,phi)) (act b v (i,phi))
         VGlue a ts              -> glue (act b a (i,phi)) (act b ts (i,phi))
         VGlueElem a ts          -> glueElem (act b a (i,phi)) (act b ts (i,phi))
         VUnGlueElem a bb ts     -> unglue (act b a (i,phi)) (act b bb (i,phi)) (act b ts (i,phi))
         VUnGlueElemU a bb es    -> unglueU (act b a (i,phi)) (act b bb (i,phi)) (act b es (i,phi))
         VHCompU a ts            -> hcompUniv (act b a (i,phi)) (act b ts (i,phi))
         VIdPair u us            -> VIdPair (act b u (i,phi)) (act b us (i,phi))
         VId a u v               -> VId (act b a (i,phi)) (act b u (i,phi)) (act b v (i,phi))
         VIdJ a u c d x p        ->
           idJ (act b a (i,phi)) (act b u (i,phi)) (act b c (i,phi)) (act b d (i,phi)) (act b x (i,phi)) (act b p (i,phi))
    | otherwise = case u of
         VU           -> VU
         Ter t e      -> Ter t (act b e (i,phi))
         VPi a f      -> VPi (act b a (i,phi)) (act b f (i,phi))
         VPathP a u v -> VPathP (act b a (i,phi)) (act b u (i,phi)) (act b v (i,phi))
         VPLam j v | j == i -> u
                   | not (j `occurs` phi) -> VPLam j (act b v (i,phi))
                   | otherwise -> VPLam k (act b (v `swap` (j,k)) (i,phi))
              where k = fresh (v,Atom i,phi)
         VSigma a f              -> VSigma (act b a (i,phi)) (act b f (i,phi))
         VPair u v               -> VPair (act b u (i,phi)) (act b v (i,phi))
         VFst u                  -> VFst (act b u (i,phi))
         VSnd u                  -> VSnd (act b u (i,phi))
         VCon c vs               -> VCon c (act b vs (i,phi))
         VPCon c a vs phis       -> VPCon c (act b a (i,phi)) (act b vs (i,phi)) (act b phis (i,phi))
         VHComp a u us           -> VHComp (act b a (i,phi)) (act b u (i,phi)) (act b us (i,phi))
         VTrans a psi u          -> VTrans (act b a (i,phi)) (act b psi (i,phi)) (act b u (i,phi))
         VVar x v                -> VVar x (act b v (i,phi))
         VOpaque x v             -> VOpaque x (act b v (i,phi))
         VAppFormula u psi       -> VAppFormula (act b u (i,phi)) (act b psi (i,phi))
         VApp u v                -> VApp (act b u (i,phi)) (act b v (i,phi))
         VLam x t u              -> VLam x (act b t (i,phi)) (act b u (i,phi))
         VSplit u v              -> VSplit (act b u (i,phi)) (act b v (i,phi))
         VGlue a ts              -> VGlue (act b a (i,phi)) (act b ts (i,phi))
         VGlueElem a ts          -> VGlueElem (act b a (i,phi)) (act b ts (i,phi))
         VUnGlueElem a bb ts     -> VUnGlueElem (act b a (i,phi)) (act b bb (i,phi)) (act b ts (i,phi))
         VUnGlueElemU a bb es    -> VUnGlueElemU (act b a (i,phi)) (act b bb (i,phi)) (act b es (i,phi))
         VHCompU a ts            -> VHCompU (act b a (i,phi)) (act b ts (i,phi))
         VIdPair u us            -> VIdPair (act b u (i,phi)) (act b us (i,phi))
         VId a u v               -> VId (act b a (i,phi)) (act b u (i,phi)) (act b v (i,phi))
         VIdJ a u c d x p        ->
           VIdJ (act b a (i,phi)) (act b u (i,phi)) (act b c (i,phi)) (act b d (i,phi)) (act b x (i,phi)) (act b p (i,phi))

  -- This increases efficiency as it won't trigger computation.
  swap u ij@(i,j) =
    let sw :: Nominal a => a -> a
        sw u = swap u ij
    in case u of
         VU                      -> VU
         Ter t e                 -> Ter t (sw e)
         VPi a f                 -> VPi (sw a) (sw f)
         VPathP a u v            -> VPathP (sw a) (sw u) (sw v)
         VPLam k v               -> VPLam (swapName k ij) (sw v)
         VSigma a f              -> VSigma (sw a) (sw f)
         VPair u v               -> VPair (sw u) (sw v)
         VFst u                  -> VFst (sw u)
         VSnd u                  -> VSnd (sw u)
         VCon c vs               -> VCon c (sw vs)
         VPCon c a vs phis       -> VPCon c (sw a) (sw vs) (sw phis)
         VHComp a u us           -> VHComp (sw a) (sw u) (sw us)
         VTrans a phi u          -> VTrans (sw a) (sw phi) (sw u)
         VVar x v                -> VVar x (sw v)
         VOpaque x v             -> VOpaque x (sw v)
         VAppFormula u psi       -> VAppFormula (sw u) (sw psi)
         VApp u v                -> VApp (sw u) (sw v)
         VLam x u v              -> VLam x (sw u) (sw v)
         VSplit u v              -> VSplit (sw u) (sw v)
         VGlue a ts              -> VGlue (sw a) (sw ts)
         VGlueElem a ts          -> VGlueElem (sw a) (sw ts)
         VUnGlueElem a b ts      -> VUnGlueElem (sw a) (sw b) (sw ts)
         VUnGlueElemU a b es     -> VUnGlueElemU (sw a) (sw b) (sw es)
         VHCompU a ts            -> VHCompU (sw a) (sw ts)
         VIdPair u us            -> VIdPair (sw u) (sw us)
         VId a u v               -> VId (sw a) (sw u) (sw v)
         VIdJ a u c d x p        ->
           VIdJ (sw a) (sw u) (sw c) (sw d) (sw x) (sw p)

-----------------------------------------------------------------------
-- The evaluator

eval :: Env -> Ter -> Val
eval rho@(Env (_,_,_,Nameless os)) v = case v of
  U                   -> VU
  App r s             -> app (eval rho r) (eval rho s)
  Var i
    | i `Set.member` os -> VOpaque i (lookType i rho)
    | otherwise       -> look i rho
  Pi t@(Lam _ a _)    -> VPi (eval rho a) (eval rho t)
  Sigma t@(Lam _ a _) -> VSigma (eval rho a) (eval rho t)
  Pair a b            -> VPair (eval rho a) (eval rho b)
  Fst a               -> fstVal (eval rho a)
  Snd a               -> sndVal (eval rho a)
  Where t decls       -> eval (defWhere decls rho) t
  Con name ts         -> VCon name (map (eval rho) ts)
  PCon name a ts phis ->
    pcon name (eval rho a) (map (eval rho) ts) (map (evalFormula rho) phis)
  Lam{}               -> Ter v rho
  Split{}             -> Ter v rho
  Sum{}               -> Ter v rho
  HSum{}              -> Ter v rho
  Undef{}             -> Ter v rho
  Hole{}              -> Ter v rho
  PathP a e0 e1       -> VPathP (eval rho a) (eval rho e0) (eval rho e1)
  PLam i t            -> let j = fresh rho
                         in VPLam j (eval (sub (i,Atom j) rho) t)
  AppFormula e phi    -> eval rho e @@ evalFormula rho phi
  HComp a t0 ts       ->
    hcompLine (eval rho a) (eval rho t0) (evalSystem rho ts)
  HFill a t0 ts       ->
    hfillLine (eval rho a) (eval rho t0) (evalSystem rho ts)
  Trans a phi t       ->
    transLine (eval rho a) (evalFormula rho phi) (eval rho t)
  Comp a t0 ts        ->
    compLine (eval rho a) (eval rho t0) (evalSystem rho ts)
  Fill a t0 ts        ->
    fillLine (eval rho a) (eval rho t0) (evalSystem rho ts)
  Glue a ts           -> glue (eval rho a) (evalSystem rho ts)
  GlueElem a ts       -> glueElem (eval rho a) (evalSystem rho ts)
  UnGlueElem v a ts   -> unglue (eval rho v) (eval rho a) (evalSystem rho ts)
  Id a r s            -> VId (eval rho a) (eval rho r) (eval rho s)
  IdPair b ts         -> VIdPair (eval rho b) (evalSystem rho ts)
  IdJ a t c d x p     -> idJ (eval rho a) (eval rho t) (eval rho c)
                             (eval rho d) (eval rho x) (eval rho p)
  _                   -> error $ "Cannot evaluate " ++ show v

evals :: Env -> [(Ident,Ter)] -> [(Ident,Val)]
evals env bts = [ (b,eval env t) | (b,t) <- bts ]

evalFormula :: Env -> Formula -> Formula
evalFormula rho phi = case phi of
  Atom i         -> lookName i rho
  NegAtom i      -> negFormula (lookName i rho)
  phi1 :/\: phi2 -> evalFormula rho phi1 `andFormula` evalFormula rho phi2
  phi1 :\/: phi2 -> evalFormula rho phi1 `orFormula` evalFormula rho phi2
  _              -> phi

evalSystem :: Env -> System Ter -> System Val
evalSystem rho ts =
  let out = concat [ let betas = meetss [ invFormula (lookName i rho) d
                                        | (i,d) <- assocs alpha ]
                     in [ (beta,eval (rho `face` beta) talpha) | beta <- betas ]
                   | (alpha,talpha) <- assocs ts ]
  in mkSystem out

app :: Val -> Val -> Val
app u v = case (u,v) of
  (Ter (Lam x _ t) e,_) -> eval (upd (x,v) e) t
  (Ter (Split _ _ _ nvs) e,VCon c vs) -> case lookupBranch c nvs of
    Just (OBranch _ xs t) -> eval (upds (zip xs vs) e) t
    _     -> error $ "app: missing case in split for " ++ c
  (Ter (Split _ _ _ nvs) e,VPCon c _ us phis) -> case lookupBranch c nvs of
    Just (PBranch _ xs is t) -> eval (subs (zip is phis) (upds (zip xs us) e)) t
    _ -> error $ "app: missing case in split for " ++ c
  (Ter (Split _ _ ty hbr) e,VHComp (Ter (Sum _ _ _) _) w ws) -> VApp u v
  (Ter (Split _ _ ty hbr) e,VHComp a w ws) -> case eval e ty of
    VPi _ f -> let j   = fresh (e,v)
                   wsj = Map.map (@@@ j) ws
                   w'  = app u w
                   ws' = mapWithKey (\alpha -> app (u `face` alpha)) wsj
                   -- a should be constant
               in comp j (app f (hfill j a w wsj)) w' ws'
    _ -> error $ "app: Split annotation not a Pi type " ++ show u
  (Ter Split{} _,_) -- | isNeutral v
                    -> VSplit u v
  (VTrans (VPLam i (VPi a f)) phi u0, v) ->
    let j = fresh (u,v)
        (aij,fij) = (a,f) `swap` (i,j)
        w = transFillNeg j aij phi v
        w0 = transNeg j aij phi v  -- w0 = w `face` (j ~> 0)
    in trans j (app fij w) phi (app u0 w0)
  (VHComp (VPi a f) u0 us, v) ->
    let i = fresh (u,v)
    in hcomp i (app f v) (app u0 v)
          (mapWithKey (\al ual -> app (ual @@@ i) (v `face` al)) us)
--  _ | isNeutral u       -> VApp u v
  _                     -> VApp u v -- error $ "app \n  " ++ show u ++ "\n  " ++ show v

fstVal, sndVal :: Val -> Val
fstVal (VPair a b)     = a
-- fstVal u | isNeutral u = VFst u
fstVal u               = VFst u -- error $ "fstVal: " ++ show u ++ " is not neutral."
sndVal (VPair a b)     = b
-- sndVal u | isNeutral u = VSnd u
sndVal u               = VSnd u -- error $ "sndVal: " ++ show u ++ " is not neutral."

-- infer the type of a neutral value
inferType :: Val -> Val
inferType v = case v of
  VVar _ t -> t
  VOpaque _ t -> t
  Ter (Undef _ t) rho -> eval rho t
  VFst t -> case inferType t of
    VSigma a _ -> a
    ty         -> error $ "inferType: expected Sigma type for " ++ show v
                  ++ ", got " ++ show ty
  VSnd t -> case inferType t of
    VSigma _ f -> app f (VFst t)
    ty         -> error $ "inferType: expected Sigma type for " ++ show v
                  ++ ", got " ++ show ty
  VSplit s@(Ter (Split _ _ t _) rho) v1 -> case eval rho t of
    VPi _ f -> app f v1
    ty      -> error $ "inferType: Pi type expected for split annotation in "
               ++ show v ++ ", got " ++ show ty
  VApp t0 t1 -> case inferType t0 of
    VPi _ f -> app f t1
    ty      -> error $ "inferType: expected Pi type for " ++ show v
               ++ ", got " ++ show ty
  VAppFormula t phi -> case inferType t of
    VPathP a _ _ -> a @@ phi
    ty         -> error $ "inferType: expected PathP type for " ++ show v
                  ++ ", got " ++ show ty
  VHComp a _ _ -> a
  VTrans a _ _ -> a @@ One
  VUnGlueElem _ b _  -> b
  VUnGlueElemU _ b _ -> b
  VIdJ _ _ c _ x p -> app (app c x) p
  _ -> error $ "inferType: not neutral " ++ show v

(@@) :: ToFormula a => Val -> a -> Val
(VPLam i u) @@ phi         = case toFormula phi of
  Dir d -> act True u (i,Dir d)
  x -> act False u (i,x)
v@(Ter Hole{} _) @@ phi    = VAppFormula v (toFormula phi)
v @@ phi -- | isNeutral v
         = case (inferType v,toFormula phi) of
  (VPathP _ a0 _,Dir 0) -> a0
  (VPathP _ _ a1,Dir 1) -> a1
  _                    -> VAppFormula v (toFormula phi)
-- v @@ phi                   = error $ "(@@): " ++ show v ++ " should be neutral."

-- Applying a *fresh* name.
(@@@) :: Val -> Name -> Val
(VPLam i u) @@@ j = u `swap` (i,j)
v @@@ j           = VAppFormula v (toFormula j)


-------------------------------------------------------------------------------
-- Composition and filling

hcompLine :: Val -> Val -> System Val -> Val
hcompLine a u us = hcomp i a u (Map.map (@@@ i) us)
  where i = fresh (a,u,us)

hfill :: Name -> Val -> Val -> System Val -> Val
hfill i a u us = hcomp j a u (insertSystem (i ~> 0) u $ us `conj` (i,j))
  where j = fresh (Atom i,a,u,us)

hfillLine :: Val -> Val -> System Val -> Val
hfillLine a u us = VPLam i $ hfill i a u (Map.map (@@@ i) us)
  where i = fresh (a,u,us)

hcomp :: Name -> Val -> Val -> System Val -> Val
hcomp i a u us | eps `member` us = (us ! eps) `face` (i ~> 1)
hcomp i a u us = case a of
  VPathP p v0 v1 -> let j = fresh (Atom i,a,u,us) in
    VPLam j $ hcomp i (p @@@ j) (u @@@ j) (insertsSystem [(j ~> 0,v0),(j ~> 1,v1)]
                                         (Map.map (@@@ j) us))
  VId b v0 v1 -> undefined
  VSigma a f -> let (us1, us2) = (Map.map fstVal us, Map.map sndVal us)
                    (u1, u2) = (fstVal u, sndVal u)
                    u1fill = hfill i a u1 us1
                    u1comp = hcomp i a u1 us1
                in VPair u1comp (comp i (app f u1fill) u2 us2)
  VU -> hcompUniv u (Map.map (VPLam i) us)
  -- TODO: neutrality tests in the next two cases could be removed
  -- since there are neutral values for unglue and unglueU
  VGlue b equivs -> -- | not (isNeutralGlueHComp equivs u us) ->
    let wts = mapWithKey (\al wal ->
                  app (equivFun wal)
                    (hfill i (equivDom wal) (u `face` al) (us `face` al)))
                equivs
        t1s = mapWithKey (\al wal ->
                hcomp i (equivDom wal) (u `face` al) (us `face` al)) equivs
        v = unglue u b equivs
        vs = mapWithKey (\al ual -> unglue ual (b `face` al) (equivs `face` al))
               us
        v1 = hcomp i b v (vs `unionSystem` wts)
    in glueElem v1 t1s
  VHCompU b es -> -- | not (isNeutralGlueHComp es u us) ->
    let wts = mapWithKey (\al eal ->
                  eqFun eal
                    (hfill i (eal @@ One) (u `face` al) (us `face` al)))
                es
        t1s = mapWithKey (\al eal ->
                hcomp i (eal @@ One) (u `face` al) (us `face` al)) es
        v = unglueU u b es
        vs = mapWithKey (\al ual -> unglueU ual (b `face` al) (es `face` al))
               us
        v1 = hcomp i b v (vs `unionSystem` wts)
    in glueElem v1 t1s
  -- Ter (Sum _ "Z" nass) env -> u
  -- Ter (Sum _ "nat" nass) env -> u  
  Ter (Sum _ _ nass) env | VCon n vs <- u, all isCon (elems us) ->
    case lookupLabel n nass of
      Just as -> let usvs = transposeSystemAndList (Map.map unCon us) vs
                     -- TODO: it is not really much of an improvement
                     -- to use hcomps here; directly use comps?
                 in VCon n $ hcomps i as env usvs
      Nothing -> error $ "hcomp: missing constructor in sum " ++ n
  Ter (HSum _ _ _) _ -> VHComp a u (Map.map (VPLam i) us)
  VPi{} -> VHComp a u (Map.map (VPLam i) us)
  _ -> VHComp a u (Map.map (VPLam i) us)

-- TODO: has to use comps after the second component anyway... remove?
hcomps :: Name -> [(Ident,Ter)] -> Env -> [(System Val,Val)] -> [Val]
hcomps i []         _ []            = []
hcomps i ((x,a):as) e ((ts,u):tsus) =
  let v   = hfill i (eval e a) u ts
      vi1 = hcomp i (eval e a) u ts
      vs  = comps i as (upd (x,v) e) tsus -- NB: not hcomps
  in vi1 : vs
hcomps _ _ _ _ = error "hcomps: different lengths of types and values"


-- For i:II |- a, phi # i, u : a (i/phi) we get fwd i a phi u : a(i/1)
-- such that fwd i a 1 u = u.   Note that i gets bound.
fwd :: Name -> Val -> Formula -> Val -> Val
fwd i a phi u = trans i (act False a (i,phi `orFormula` Atom i)) phi u

comp :: Name -> Val -> Val -> System Val -> Val
-- comp i a u us = hcomp i (a `face` (i ~> 1)) (fwd i a (Dir Zero) u) fwdius
--  where fwdius = mapWithKey (\al ual -> fwd i (a `face` al) (Atom i) ual) us

-- comp i a u ts | eps `member` ts = (ts ! eps) `face` (i ~> 1)
comp i a u ts =
  let j = fresh (Atom i,a,u,ts)
  in case a of
    -- VPathP p v0 v1 ->
    --   VPLam j $ comp i (p @@@ j) (u @@@ j) $
    --               insertsSystem [(j ~> 0,v0),(j ~> 1,v1)] (Map.map (@@@ j) ts)
    _ -> hcomp j (a `face` (i ~> 1)) (fwd i a (Dir Zero) u)
               (mapWithKey (\al ual -> fwd i (a `face` al) (Atom j) (ual  `swap` (i,j))) ts)

compNeg :: Name -> Val -> Val -> System Val -> Val
compNeg i a u ts = comp i (a `sym` i) u (ts `sym` i)

compLine :: Val -> Val -> System Val -> Val
compLine a u ts = comp i (a @@@ i) u (Map.map (@@@ i) ts)
  where i = fresh (a,u,ts)

comps :: Name -> [(Ident,Ter)] -> Env -> [(System Val,Val)] -> [Val]
comps i []         _ []         = []
comps i ((x,a):as) e ((ts,u):tsus) =
  let v   = fill i (eval e a) u ts
      vi1 = comp i (eval e a) u ts
      vs  = comps i as (upd (x,v) e) tsus
  in vi1 : vs
comps _ _ _ _ = error "comps: different lengths of types and values"

fill :: Name -> Val -> Val -> System Val -> Val
fill i a u ts =
  comp j (a `conj` (i,j)) u (insertSystem (i ~> 0) u (ts `conj` (i,j)))
  where j = fresh (Atom i,a,u,ts)

fillNeg :: Name -> Val -> Val -> System Val -> Val
fillNeg i a u ts = (fill i (a `sym` i) u (ts `sym` i)) `sym` i

fillLine :: Val -> Val -> System Val -> Val
fillLine a u ts = VPLam i $ fill i (a @@@ i) u (Map.map (@@@ i) ts)
  where i = fresh (a,u,ts)


-----------------------------------------------------------
-- Transport and forward

transLine :: Val -> Formula -> Val -> Val
transLine a phi u = trans i (a @@@ i) phi u
  where i = fresh (a,phi,u)

-- For i:II |- a, phi # i,
--     i:II, phi=1 |- a = a(i/0)
-- and u : a(i/0) gives trans i a phi u : a(i/1) such that
-- trans i a 1 u = u : a(i/1) (= a(i/0)).
trans :: Name -> Val -> Formula -> Val -> Val
trans i a (Dir One) u = u
trans i a phi u = case a of
  VPathP p v0 v1 -> let j = fresh (Atom i,a,phi,u) in
    VPLam j $ comp i (p @@@ j) (u @@@ j) (insertsSystem [(j ~> 0,v0),(j ~> 1,v1)]
                                         (border (u @@@ j) (invSystem phi One)))
  VId b v0 v1 -> undefined
  VSigma a f ->
    let (u1,u2) = (fstVal u, sndVal u)
        u1f     = transFill i a phi u1
    in VPair (trans i a phi u1) (trans i (app f u1f) phi u2)
  VPi{} -> VTrans (VPLam i a) phi u
  VU -> u
  -- TODO: neutrality tests in the next two cases could be removed
  -- since there are neutral values for unglue and unglueU
  VGlue b equivs -> -- | not (eps `notMember` (equivs `face` (i ~> 0)) && isNeutral u) ->
    transGlue i b equivs phi u
  VHCompU b es -> -- | not (eps `notMember` (es `face` (i ~> 0)) && isNeutral u) ->
    transHCompU i b es phi u
  Ter (Sum _ n nass) env
    | n `elem` ["nat","Z","bool"] -> u -- hardcode hack
    | otherwise -> case u of
    VCon n us -> case lookupLabel n nass of
      Just tele -> VCon n (transps i tele env phi us)
      Nothing -> error $ "trans: missing constructor in sum " ++ n
    _ -> VTrans (VPLam i a) phi u
  Ter (HSum _ n nass) env
    | n `elem` ["S1","S2","S3"] -> u
    | otherwise -> case u of
    VCon n us -> case lookupLabel n nass of
      Just tele -> VCon n (transps i tele env phi us)
      Nothing -> error $ "trans: missing constructor in hsum " ++ n
    VPCon n _ us psis -> case lookupPLabel n nass of
      Just (tele,is,es) ->
        let ai1  = a `face` (i ~> 1)
            vs   = transFills i tele env phi us
            env' = subs (zip is psis) (updsTele tele vs env)
            ves  = evalSystem env' es
            ves' = mapWithKey
                   (\al veal -> squeeze i (a `face` al) (phi `face` al) veal)
                   ves
            pc = VPCon n ai1 (transps i tele env phi us) psis
            -- NB: restricted to phi=1, u = pc; so we could also take pc instead
            uphi = border u (invSystem phi One)
        in pc
           --hcomp i ai1 pc ((ves' `sym` i) `unionSystem` uphi)
      Nothing -> error $ "trans: missing path constructor in hsum " ++ n
    VHComp _ v vs -> let j = fresh (Atom i,a,phi,u) in
      hcomp j (a `face` (i ~> 1)) (trans i a phi v)
        (mapWithKey (\al val ->
                      trans i (a `face` al) (phi `face` al) (val @@@ j)) vs)
    _ -> VTrans (VPLam i a) phi u
  _ -> VTrans (VPLam i a) phi u


transFill :: Name -> Val -> Formula -> Val -> Val
transFill i a phi u = trans j (a `conj` (i,j)) (phi `orFormula` NegAtom i) u
  where j = fresh (Atom i,a,phi,u)

transFills :: Name ->  [(Ident,Ter)] -> Env -> Formula -> [Val] -> [Val]
transFills i []         _ phi []     = []
transFills i ((x,a):as) e phi (u:us) =
  let v = transFill i (eval e a) phi u
  in v : transFills i as (upd (x,v) e) phi us

transNeg :: Name -> Val -> Formula -> Val -> Val
transNeg i a phi u = trans i (a `sym` i) phi u

transFillNeg :: Name -> Val -> Formula -> Val -> Val
transFillNeg i a phi u = (transFill i (a `sym` i) phi u) `sym` i

transNegLine :: Val -> Formula -> Val -> Val
transNegLine u phi v = transNeg i (u @@@ i) phi v
  where i = fresh (u,phi,v)

transps :: Name -> [(Ident,Ter)] -> Env -> Formula -> [Val] -> [Val]
transps i []         _ phi []     = []
transps i ((x,a):as) e phi (u:us) =
  let v   = transFill i (eval e a) phi u
      vi1 = trans i (eval e a) phi u
      vs  = transps i as (upd (x,v) e) phi us
  in vi1 : vs
transps _ _ _ _ _ = error "transps: different lengths of types and values"

-- Takes a type i : II |- a and i:II |- u : a, both constant on
-- (phi=1) and returns a path in direction i connecting transp i a phi
-- u(i/0) to u(i/1).
squeeze :: Name -> Val -> Formula -> Val -> Val
squeeze i a phi u = trans j (a `disj` (i,j)) (phi `orFormula` Atom i) u
  where j = fresh (Atom i,a,phi,u)


-------------------------------------------------------------------------------
-- | Id

idJ :: Val -> Val -> Val -> Val -> Val -> Val -> Val
idJ a v c d x p = case p of
  VIdPair w ws -> comp i (app (app c (w @@ i)) w') d
                    (border d (shape ws))
    where w' = VIdPair (VPLam j $ w @@ (Atom i :/\: Atom j))
                  (insertSystem (i ~> 0) v ws)
          i:j:_ = freshs [a,v,c,d,x,p]
  _ -> VIdJ a v c d x p

isIdPair :: Val -> Bool
isIdPair VIdPair{} = True
isIdPair _         = False


-------------------------------------------------------------------------------
-- | HITs

pcon :: LIdent -> Val -> [Val] -> [Formula] -> Val
pcon c a@(Ter (HSum _ _ lbls) rho) us phis = case lookupPLabel c lbls of
  Just (tele,is,ts) | eps `member` vs -> vs ! eps
                    | otherwise       -> VPCon c a us phis
    where rho' = subs (zip is phis) (updsTele tele us rho)
          vs   = evalSystem rho' ts
  Nothing           -> error "pcon"
pcon c a us phi     = VPCon c a us phi


-------------------------------------------------------------------------------
-- | Glue

-- An equivalence for a type a is a triple (t,f,p) where
-- t : U
-- f : t -> a
-- p : (x : a) -> isContr ((y:t) * Path a x (f y))
-- with isContr c = (z : c) * ((z' : C) -> Path c z z')

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
glueElem v us | eps `member` us = us ! eps
glueElem v us = VGlueElem v us

unglue :: Val -> Val -> System Val -> Val
unglue w a equivs | eps `member` equivs = app (equivFun (equivs ! eps)) w
unglue (VGlueElem v us) _ _ = v
unglue w a equivs = VUnGlueElem w a equivs

-- isNeutralGlueHComp :: System Val -> Val -> System Val -> Bool
-- isNeutralGlueHComp equivs u us =
--   (eps `notMember` equivs && isNeutral u) ||
--   any (\(alpha,uAlpha) -> eps `notMember` (equivs `face` alpha)
--         && isNeutral uAlpha) (assocs us)

transGlue :: Name -> Val -> System Val -> Formula -> Val -> Val
transGlue i a equivs psi u0 = glueElem v1' t1s'
  where
    (ai0,equivsi0) = (a,equivs) `face` (i ~> 0)
    (ai1,equivsi1) = (a,equivs) `face` (i ~> 1)

    v0 = unglue u0 ai0 equivsi0

    alliequivs = allSystem i equivs
    psisys = invSystem psi One -- (psi = 1) : FF

    alliequivs' =
      mapWithKey (\al wal -> (equivFun wal,equivDom wal,psi `face` al,u0 `face` al))
                 alliequivs

    t1s = Map.map (\(fwal,dwal,psial,u0al) -> (fwal,trans i dwal psial u0al)) alliequivs'
    wts = Map.map (\(fwal,dwal,psial,u0al) -> app fwal (transFill i dwal psial u0al)) alliequivs'

    v1 = comp i a v0 (border v0 psisys `unionSystem` wts)

    fibersys = border (VPair u0 (constPath v0)) psisys `unionSystem`
               Map.map (\(fwal,x) -> VPair x (constPath (app fwal x))) t1s

    fibersys' = mapWithKey
                  (\al wal ->
                    let (a,b,f,y) = (equivDom wal,ai1 `face` al,equivFun wal,v1 `face` al)
                        c12 = app (equivContr wal) y
                        (c1,c2) = (fstVal c12,sndVal c12)
                        us = mapWithKey (\alpha tAlpha -> app (c2 `face` alpha) tAlpha @@ i) (fibersys `face` al)
                    in hcompFiber i a b f y c1 us)
                     -- extend (mkFiberType (ai1 `face` al) (v1 `face` al) wal)
                     --        (app (equivContr wal) (v1 `face` al))
                     --        (fibersys `face` al))
                  equivsi1

    t1s' = Map.map fstVal fibersys'
    -- no need for a fresh name; take i
    v1' = hcomp i ai1 v1 (Map.map (\om -> (sndVal om) @@ i) fibersys'
                           `unionSystem` border v1 psisys)

-- Unfolded version of "hcomp i (Fiber a b f y) u us" implementing:
--
-- hcomp^i (Fiber A B f y) [phi -> us] u =
--   (hcomp^i A u.1 [phi -> us.1]
--   ,<j> hcomp^i B (u.2 @@ i) [phi -> us.2 @ i, (j=0) -> y, (j=1) -> f (hfill^i A u.1 [phi -> us.1])])
--
hcompFiber :: Name -> Val -> Val -> Val -> Val -> Val -> System Val -> Val
hcompFiber i a b f y u us =
  let (u1,u2,us1,us2) = (fstVal u,sndVal u,Map.map fstVal us,Map.map sndVal us)
      u1comp = hcomp i a u1 us1
      u1fill = hfill i a u1 us1
      j = fresh ()
  in VPair u1comp (VPLam j $ hcomp i b (u2 @@@ j)
                                       (insertsSystem [(j~>0, y),(j~>1,app f u1fill)]
                                                      (Map.map (@@ i) us2)))

-- -- Extend the system ts to a total element in b given q : isContr b
-- extend :: Val -> Val -> System Val -> Val
-- extend b q ts = hcomp i b (fstVal q) ts'
--   where i = fresh (b,q,ts)
--         ts' = mapWithKey
--                 (\alpha tAlpha -> app ((sndVal q) `face` alpha) tAlpha @@ i) ts

-- mkFiberType :: Val -> Val -> Val -> Val
-- mkFiberType a x equiv = eval rho $
--   Sigma $ Lam "y" tt (PathP (PLam (Name "_") ta) tx (App tf ty))
--   where [ta,tx,ty,tf,tt] = map Var ["a","x","y","f","t"]
--         rho = upds [("a",a),("x",x),("f",equivFun equiv)
--                    ,("t",equivDom equiv)] emptyEnv

-- -- Assumes u' : A is a solution of us + (i0 -> u0)
-- -- The output is an L-path in A(i1) between comp i u0 us and u'(i1)
-- pathcomp :: Name -> Val -> Val -> Val -> System Val -> Val
-- pathcomp i a u0 u' us = VPLam j $ comp i a u0 us'
--   where j   = fresh (Atom i,a,us,u0,u')
--         us' = insertsSystem [(j ~> 1, u')] us

-------------------------------------------------------------------------------
-- | Composition in the Universe

-- any path between types define an equivalence
eqFun :: Val -> Val -> Val
eqFun e = transNegLine e (Dir Zero)

unglueU :: Val -> Val -> System Val -> Val
unglueU w b es | eps `Map.member` es = eqFun (es ! eps) w
unglueU (VGlueElem v us) _ _ = v
unglueU w b es = VUnGlueElemU w b es

hcompUniv :: Val -> System Val -> Val
hcompUniv b es | eps `Map.member` es = (es ! eps) @@ One
               | otherwise           = VHCompU b es

transHCompU :: Name -> Val -> System Val -> Formula -> Val -> Val
transHCompU i a es psi u0 = glueElem v1' t1s'
  where
    (ai0,esi0) = (a,es) `face` (i ~> 0)
    (ai1,esi1) = (a,es) `face` (i ~> 1)

    v0 = unglueU u0 ai0 esi0

    allies = allSystem i es
    psisys = invSystem psi One -- (psi = 1) : FF

    -- Preprocess allies to avoid recomputing the faces in t1s and wts
    allies' = mapWithKey (\al eal ->
                (eal, eal @@ One, psi `face` al, u0 `face` al)) allies
    t1s = Map.map
            (\(_,eal1,psial,u0al) -> trans i eal1 psial u0al)
            allies'
    wts = Map.map
            (\(eal,eal1,psial,u0al) -> eqFun eal (transFill i eal1 psial u0al))
            allies'

    v1 = comp i a v0 (border v0 psisys `unionSystem` wts)

    sys = border u0 psisys `unionSystem` t1s

    fibersys' = mapWithKey
                  (\al eal ->
--                     lemEq' eal (v1 `face` al) (sys `face` al))
                     lemEqConst i eal (v1 `face` al) (sys `face` al))
                  esi1

    t1s' = Map.map fst fibersys'

    v1' = hcomp i ai1 v1 (Map.map snd fibersys' `unionSystem` border v1 psisys)

-- Extend a partial element (aalpha, <_> f aalpha) in the fiber over b
-- to a total one where f is transNeg of eq.  Applies the second
-- component to the fresh name i.
lemEqConst :: Name -> Val -> Val -> System Val -> (Val,Val)
lemEqConst i eq b as = (a,p)
 where
   j = fresh (eq,b,as)
   eqj = eq @@@ j
   adwns = mapWithKey (\al aal ->
               let eqaj = eqj `face` al
               in transFillNeg j eqaj (Dir Zero) aal) as
   left = fill j eqj b adwns
   a = comp j eqj b adwns
   -- a = left `face` (j ~> 1)

   right = transFillNeg j eqj (Dir Zero) a

   p = compNeg j eqj a (insertsSystem [ (i ~> 0, left), (i ~> 1, right)] adwns)



-- -- TODO: check; can probably be optimized
-- lemEq' :: Val -> Val -> System Val -> (Val,Val)
-- lemEq' eq b as = (a,VPLam i (compNeg j (eq @@ j) p1 thetas'))
--  where
--    i:j:_ = freshs (eq,b,as)
--    ta = eq @@ One
--    p1s = mapWithKey (\alpha aa ->
--               let eqaj = (eq `face` alpha) @@ j
--                   pa = transNeg j eqaj (Dir Zero) aa
--                   ba = b `face` alpha
--               in comp j eqaj pa
--                    (mkSystem [ (i~>0,transFill j eqaj (Dir Zero) ba)
--                              , (i~>1,transFillNeg j eqaj (Dir Zero) aa)])) as
--    thetas = mapWithKey (\alpha aa ->
--               let eqaj = (eq `face` alpha) @@ j
--                   pa = transNeg j eqaj (Dir Zero) aa
--                   ba = b `face` alpha
--               in fill j eqaj pa
--                    (mkSystem [ (i~>0,transFill j eqaj (Dir Zero) ba)
--                              , (i~>1,transFillNeg j eqaj (Dir Zero) aa)])) as

--    a  = hcomp i ta (trans i (eq @@ i) (Dir Zero) b) p1s
--    p1 = hfill i ta (trans i (eq @@ i) (Dir Zero) b) p1s

--    thetas' = insertsSystem
--                [ (i ~> 0,transFill j (eq @@ j) (Dir Zero) b)
--                , (i ~> 1,transFillNeg j (eq @@ j) (Dir Zero) a)]
--                thetas



-------------------------------------------------------------------------------
-- | Conversion

class Convertible a where
  conv :: [String] -> a -> a -> Bool

conflictCompSystem :: (Nominal a, Convertible a) => [String] -> System a -> [(a,a)]
conflictCompSystem ns ts =
  [ (fa, fb) | (alpha,beta) <- allCompatible (keys ts),
               let (fa,fb) = (getFace alpha beta, getFace beta alpha),
               not (conv ns fa fb) ]
  where getFace a b = face (ts ! a) (b `minus` a)

isCompSystem :: (Nominal a, Convertible a) => [String] -> System a -> Bool
isCompSystem ns ts = null (conflictCompSystem ns ts)

instance Convertible Env where
  conv ns (Env (rho1,vs1,fs1,os1)) (Env (rho2,vs2,fs2,os2)) =
      conv ns (rho1,vs1,fs1,os1) (rho2,vs2,fs2,os2)

instance Convertible Val where
  conv ns u v | u == v    = True
              | otherwise =
    let j = fresh (u,v)
    in case (u,v) of
      (Ter (Lam x a u) e,Ter (Lam x' a' u') e') ->
        let v@(VVar n _) = mkVarNice ns x (eval e a)
        in conv (n:ns) (eval (upd (x,v) e) u) (eval (upd (x',v) e') u')
      (Ter (Lam x a u) e,u') ->
        let v@(VVar n _) = mkVarNice ns x (eval e a)
        in conv (n:ns) (eval (upd (x,v) e) u) (app u' v)
      (u',Ter (Lam x a u) e) ->
        let v@(VVar n _) = mkVarNice ns x (eval e a)
        in conv (n:ns) (app u' v) (eval (upd (x,v) e) u)
      (Ter (Split _ p _ _) e,Ter (Split _ p' _ _) e') -> (p == p') && conv ns e e'
      (Ter (Sum p _ _) e,Ter (Sum p' _ _) e')         -> (p == p') && conv ns e e'
      (Ter (HSum p _ _) e,Ter (HSum p' _ _) e')       -> (p == p') && conv ns e e'
      (Ter (Undef p _) e,Ter (Undef p' _) e') -> p == p' && conv ns e e'
      (Ter (Hole p) e,Ter (Hole p') e') -> p == p' && conv ns e e'
      -- (Ter Hole{} e,_) -> True
      -- (_,Ter Hole{} e') -> True
      (VPi u v,VPi u' v') ->
        let w@(VVar n _) = mkVarNice ns "X" u
        in conv ns u u' && conv (n:ns) (app v w) (app v' w)
      (VSigma u v,VSigma u' v') ->
        let w@(VVar n _) = mkVarNice ns "X" u
        in conv ns u u' && conv (n:ns) (app v w) (app v' w)
      (VCon c us,VCon c' us')   -> (c == c') && conv ns us us'
      (VPCon c v us phis,VPCon c' v' us' phis') ->
        (c == c') && conv ns (v,us,phis) (v',us',phis')
      (VPair u v,VPair u' v')    -> conv ns u u' && conv ns v v'
      (VPair u v,w)              -> conv ns u (fstVal w) && conv ns v (sndVal w)
      (w,VPair u v)              -> conv ns (fstVal w) u && conv ns (sndVal w) v
      (VFst u,VFst u')           -> conv ns u u'
      (VSnd u,VSnd u')           -> conv ns u u'
      (VApp u v,VApp u' v')      -> conv ns u u' && conv ns v v'
      (VSplit u v,VSplit u' v')  -> conv ns u u' && conv ns v v'
      (VOpaque x _, VOpaque x' _) -> x == x'
      (VVar x _, VVar x' _)       -> x == x'
      (VPathP a b c,VPathP a' b' c') -> conv ns a a' && conv ns b b' && conv ns c c'
      (VPLam i a,VPLam i' a')    -> conv ns (a `swap` (i,j)) (a' `swap` (i',j))
      (VPLam i a,p')             -> conv ns (a `swap` (i,j)) (p' @@@ j)
      (p,VPLam i' a')            -> conv ns (p @@@ j) (a' `swap` (i',j))
      (VAppFormula u x,VAppFormula u' x') -> conv ns (u,x) (u',x')
      (VTrans a phi u,VTrans a' phi' u')  ->
        -- TODO: Maybe identify via (- = 1)?  Or change argument to a system..
        conv ns (a,invSystem phi One,u) (a',invSystem phi' One,u')
        -- conv ns (a,phi,u) (a',phi',u')
      (VHComp a u ts,VHComp a' u' ts')    -> conv ns (a,u,ts) (a',u',ts')
      (VGlue v equivs,VGlue v' equivs')   -> conv ns (v,equivs) (v',equivs')
      (VGlueElem (VUnGlueElem b a equivs) ts,g) -> conv ns (border b equivs,b) (ts,g)
      (g,VGlueElem (VUnGlueElem b a equivs) ts) -> conv ns (border b equivs,b) (ts,g)
      (VGlueElem (VUnGlueElemU b a equivs) ts,g) -> conv ns (border b equivs,b) (ts,g)
      (g,VGlueElem (VUnGlueElemU b a equivs) ts) -> conv ns (border b equivs,b) (ts,g)
      (VGlueElem u us,VGlueElem u' us')   -> conv ns (u,us) (u',us')
      (VUnGlueElemU u _ _,VUnGlueElemU u' _ _) -> conv ns u u'
      (VUnGlueElem u _ _,VUnGlueElem u' _ _) -> conv ns u u'
      (VHCompU u es,VHCompU u' es')            -> conv ns (u,es) (u',es')
      (VIdPair v vs,VIdPair v' vs')          -> conv ns (v,vs) (v',vs')
      (VId a u v,VId a' u' v')               -> conv ns (a,u,v) (a',u',v')
      (VIdJ a u c d x p,VIdJ a' u' c' d' x' p') ->
        conv ns [a,u,c,d,x,p] [a',u',c',d',x',p']
      _                                      -> False

instance Convertible Ctxt where
  conv _ _ _ = True

instance Convertible () where
  conv _ _ _ = True

instance (Convertible a, Convertible b) => Convertible (a, b) where
  conv ns (u, v) (u', v') = conv ns u u' && conv ns v v'

instance (Convertible a, Convertible b, Convertible c)
      => Convertible (a, b, c) where
  conv ns (u, v, w) (u', v', w') = conv ns (u,(v,w)) (u',(v',w'))

instance (Convertible a,Convertible b,Convertible c,Convertible d)
      => Convertible (a,b,c,d) where
  conv ns (u,v,w,x) (u',v',w',x') = conv ns (u,v,(w,x)) (u',v',(w',x'))

instance Convertible a => Convertible [a] where
  conv ns us us' = length us == length us' &&
                  and [conv ns u u' | (u,u') <- zip us us']

instance Convertible a => Convertible (System a) where
  conv ns ts ts' = keys ts == keys ts' &&
                   and (elems (intersectionWith (conv ns) ts ts'))

instance Convertible Formula where
  conv _ phi psi = dnf phi == dnf psi

instance Convertible (Nameless a) where
  conv _ _ _ = True

-------------------------------------------------------------------------------
-- | Normalization

class Normal a where
  normal :: [String] -> a -> a

instance Normal Env where
  normal ns (Env (rho,vs,fs,os)) = Env (normal ns (rho,vs,fs,os))

instance Normal Val where
  normal ns v = case v of
    VU                  -> VU
    Ter (Lam x t u) e   ->
      let w = eval e t
          v@(VVar n _) = mkVarNice ns x w
      in VLam n (normal ns w) $ normal (n:ns) (eval (upd (x,v) e) u)
    Ter t e             -> Ter t (normal ns e)
    VPi u v             -> VPi (normal ns u) (normal ns v)
    VSigma u v          -> VSigma (normal ns u) (normal ns v)
    VPair u v           -> VPair (normal ns u) (normal ns v)
    VCon n us           -> VCon n (normal ns us)
    VPCon n u us phis   -> VPCon n (normal ns u) (normal ns us) phis
    VPathP a u0 u1      -> VPathP (normal ns a) (normal ns u0) (normal ns u1)
    VPLam i u           -> VPLam i (normal ns u)
    VTrans a phi u      -> VTrans (normal ns a) (normal ns phi) (normal ns u)
    VHComp u v vs       -> VHComp (normal ns u) (normal ns v) (normal ns vs)
    VGlue u equivs      -> VGlue (normal ns u) (normal ns equivs)
    VGlueElem (VUnGlueElem b _ _) _ -> normal ns b
    VGlueElem (VUnGlueElemU b _ _) _ -> normal ns b
    VGlueElem u us      -> VGlueElem (normal ns u) (normal ns us)
    VUnGlueElem v u us  -> VUnGlueElem (normal ns v) (normal ns u) (normal ns us)
    VUnGlueElemU e u us -> VUnGlueElemU (normal ns e) (normal ns u) (normal ns us)
    VHCompU a ts        -> VHCompU (normal ns a) (normal ns ts)
    VVar x t            -> VVar x (normal ns t)
    VFst t              -> VFst (normal ns t)
    VSnd t              -> VSnd (normal ns t)
    VSplit u t          -> VSplit (normal ns u) (normal ns t)
    VApp u v            -> VApp (normal ns u) (normal ns v)
    VAppFormula u phi   -> VAppFormula (normal ns u) (normal ns phi)
    VId a u v           -> VId (normal ns a) (normal ns u) (normal ns v)
    VIdPair u us        -> VIdPair (normal ns u) (normal ns us)
    VIdJ a u c d x p    -> VIdJ (normal ns a) (normal ns u) (normal ns c)
                                (normal ns d) (normal ns x) (normal ns p)
    _                   -> v

instance Normal (Nameless a) where
  normal _ = id

instance Normal Ctxt where
  normal _ = id

instance Normal Formula where
  normal _ = fromDNF . dnf

instance Normal a => Normal (Map k a) where
  normal ns = Map.map (normal ns)

instance (Normal a,Normal b) => Normal (a,b) where
  normal ns (u,v) = (normal ns u,normal ns v)

instance (Normal a,Normal b,Normal c) => Normal (a,b,c) where
  normal ns (u,v,w) = (normal ns u,normal ns v,normal ns w)

instance (Normal a,Normal b,Normal c,Normal d) => Normal (a,b,c,d) where
  normal ns (u,v,w,x) =
    (normal ns u,normal ns v,normal ns w, normal ns x)

instance Normal a => Normal [a] where
  normal ns = map (normal ns)
