module Eval where

import Data.List
import Data.Maybe (fromMaybe)

import TT

look :: String -> Env -> Val
look x (Pair rho ((y,_),u)) | x == y    = u
                            | otherwise = look x rho
look x r@(PDef es r1) = case lookupIdent x es of
  Just (_,t) -> eval r t
  Nothing -> look x r1

lookType :: String -> Env -> Val
lookType x (Pair rho ((y,_),VN (VVar _ a))) | x == y    = a
                                            | otherwise = lookType x rho
lookType x r@(PDef es r1) = case lookupIdent x es of
  Just (a,_) -> eval r a
  Nothing -> lookType x r1

eval :: Env -> Ter -> Val
eval e v = case v of
  U             -> VU
  App r s       -> app (eval e r) (eval e s)
  Var i         -> look i e
  Pi t@(Lam _ a _) -> VPi (eval e a) (eval e t)
  Lam x a t       -> Ter (Lam x a t) e
  Sigma t@(Lam _ a _) -> VSigma (eval e a) (eval e t)
  SPair a b     -> VSPair (eval e a) (eval e b)
  Fst a         -> fstVal (eval e a)
  Snd a         -> sndVal (eval e a)
  Where t decls -> eval (PDef decls e) t
  Con name ts   -> VCon name (map (eval e) ts)
  Split l t brcs  -> Ter (Split l t brcs) e
  Sum pr lbls   -> Ter (Sum pr lbls) e
  Undef l       -> error $ "eval: undefined at " ++ show l

evals :: Env -> [(Binder,Ter)] -> [(Binder,Val)]
evals env bts = [ (b,eval env t) | (b,t) <- bts ]

app :: Val -> Val -> Val
app (Ter (Lam x _ t) e) u                  = eval (Pair e (x,u)) t
app (Ter (Split _ _ nvs) e) (VCon name us) = case lookup name nvs of
  Just (xs,t) -> eval (pairs e (zip xs us)) t
  Nothing     -> error $ "app: Split with insufficient arguments; " ++
                         " missing case for " ++ name
app u@(Ter (Split _ _ _) _) (VN v) = VN (VSplit u v)
app (VN r) s = VN (VApp r s)

fstVal, sndVal :: Val -> Val
fstVal (VSPair a b) = a
fstVal (VN u)       = VN (VFst u)
sndVal (VSPair a b) = b
sndVal (VN u)       = VN (VSnd u)

-------------------------------------------------------------------------------
-- | Conversion

conv :: Int -> Val -> Val -> Bool
conv k u v | u == v    = True
           | otherwise = case (u,v) of
  (Ter (Lam x a u) e,Ter (Lam x' a' u') e') -> 
    let v = mkVar k (eval e a)
    in conv (k+1) (eval (Pair e (x,v)) u) (eval (Pair e' (x',v)) u')
  (Ter (Lam x a u) e,u') ->
    let v = mkVar k (eval e a)
    in conv (k+1) (eval (Pair e (x,v)) u) (app u' v)
  (u',Ter (Lam x a u) e) ->
    let v = mkVar k (eval e a)
    in conv (k+1) (app u' v) (eval (Pair e (x,v)) u)
  (Ter (Split p _ _) e,Ter (Split p' _ _) e') -> (p == p') && convEnv k e e'
  (Ter (Sum p _) e,Ter (Sum p' _) e')     -> (p == p') && convEnv k e e'
  (Ter (Undef p) e,Ter (Undef p') e')     -> (p == p') && convEnv k e e'
  (VPi u v,VPi u' v') ->
    let w = mkVar k u
    in conv k u u' && conv (k+1) (app v w) (app v' w)
  (VSigma u v,VSigma u' v') ->
    let w = mkVar k u
    in conv k u u' && conv (k+1) (app v w) (app v' w)
  (VCon c us,VCon c' us')   -> (c == c') && and (zipWith (conv k) us us')
  (VSPair u v,VSPair u' v') -> conv k u u' && conv k v v'
  (VSPair u v,w)            -> conv k u (fstVal w) && conv k v (sndVal w)
  (w,VSPair u v)            -> conv k (fstVal w) u && conv k (sndVal w) v
  (VN u,VN v)               -> convNeutral k u v
  _                         -> False

convNeutral :: Int -> Neutral -> Neutral -> Bool
convNeutral k u v = case (u,v) of
  (VFst u,VFst u')          -> convNeutral k u u'
  (VSnd u,VSnd u')          -> convNeutral k u u'
  (VApp u v,VApp u' v')     -> convNeutral k u u' && conv k v v'
  (VSplit u v,VSplit u' v') -> conv k u u' && convNeutral k v v'
  (VVar x _, VVar x' _)     -> x == x'

convEnv :: Int -> Env -> Env -> Bool
convEnv k e e' = and $ zipWith (conv k) (valOfEnv e) (valOfEnv e')