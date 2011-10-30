
module Main where

import Data.Char
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.ByteString.Char8 as BS
import Data.Attoparsec.Char8 as AP hiding (many)
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import Control.Arrow
import System.IO
import System.Environment

-- data types

data Term v uv n
    = TName n
    | TVar v
    | TUVar uv
    | TApp (Term v uv n) (Term v uv n)
    | TAbs v (Term v uv n)
    deriving Show

type Term' v n = Term (v, Int) v n
type StrTerm = Term String String String
type StrTerm' = Term' String String

type TermState v n = (Term' v n, Map.Map v Int)
type StrTermState = (StrTerm', Map.Map String Int)

type Zipper a = ([a], a, [a])
type History = Zipper StrTermState

data Operation
    = OpReduction Int
    | OpExpand Int
    | OpUndo
    | OpRedo
    | OpQuit
    | OpHelp
    | OpNull
    deriving Show

-- alpha conversion

alpha' :: Ord v => Term v v n ->
    ReaderT (Map.Map v Int) (State (Map.Map v Int)) (Term' v n)
alpha' (TName n) = return $ TName n
alpha' (TVar v) = asks $ maybe (TUVar v) (TVar . (,) v) . Map.lookup v
alpha' (TUVar v) = asks $ maybe (TUVar v) (TVar . (,) v) . Map.lookup v
alpha' (TApp t1 t2) = liftM2 TApp (alpha' t1) (alpha' t2)
alpha' (TAbs v t1) = do
    n <- gets $ maybe 0 succ . Map.lookup v
    modify $ Map.insert v n
    TAbs (v, n) <$> local (Map.insert v n) (alpha' t1)

alpha :: Ord v => Term v v n -> State (Map.Map v Int) (Term' v n)
alpha t = runReaderT (alpha' t) Map.empty

-- beta reduction

substitute :: Eq v => (v, Int) -> Term' v n -> Term' v n -> Term' v n
substitute v t (TVar v') | v == v' = t
substitute v t (TApp t1 t2) = TApp (substitute v t t1) (substitute v t t2)
substitute v t (TAbs v' t') | v /= v' = TAbs v' $ substitute v t t'
substitute _ _ t = t

reduction :: Eq v => Term' v n -> [Term' v n]
reduction (TApp t1 t2) =
    l ++ map (`TApp` t2) (reduction t1) ++ map (TApp t1) (reduction t2) where
    l = case t1 of
        TAbs v t3 -> [substitute v t2 t3]
        _ -> []
reduction (TAbs v t) = map (TAbs v) (reduction t)
reduction _ = []

-- expand

expand :: (Ord n, Ord v) =>
    Map.Map n (Term v v n) -> TermState v n -> [TermState v n]
expand env (TName n, st) =
    case Map.lookup n env of
        Just t -> [runState (alpha t) st]
        Nothing -> [(TName n, st)]
expand env (TApp t1 t2, st) =
    map (first (`TApp` t2)) (expand env (t1, st)) ++
    map (first (TApp t1)) (expand env (t2, st))
expand env (TAbs v t, st) = map (first (TAbs v)) (expand env (t, st))
expand env _ = []

-- free variables

fv :: Ord v => Term v v n -> Set.Set v
fv (TUVar v) = Set.singleton v
fv (TApp t1 t2) = fv t1 `Set.union` fv t2
fv (TAbs v t) = Set.delete v $ fv t
fv _ = Set.empty

-- names

names :: Ord n => Term v uv n -> Set.Set n
names (TName n) = Set.singleton n
names (TApp t1 t2) = names t1 `Set.union` names t2
names (TAbs v t) = names t
names _ = Set.empty

-- validate input

validate :: [(String, StrTerm)] -> StrTerm -> Bool
validate binds term =
    all (Set.null . fv . snd) binds &&
    Set.null (Set.difference
        (foldr (Set.union . names . snd) (names term) binds)
        (Set.fromList (map fst binds)))

-- parser

getResToken :: String -> Parser ()
getResToken str = string (BS.pack str) >> skipSpace

getLabel :: (Char -> Bool) -> Parser String
getLabel f =
    liftM2 (:) (satisfy f) (BS.unpack <$> AP.takeWhile isAlpha) <* skipSpace

getVar, getName :: Parser String
getVar = getLabel isLower
getName = getLabel isUpper

absParser, appParser, factorParser :: Parser StrTerm

absParser = do
        getResToken "\\"
        vs <- many1 getVar
        getResToken "."
        flip (foldr TAbs) vs <$> absParser
    <|> appParser

appParser = liftM2 (foldl TApp) factorParser (many factorParser)

factorParser =
    (getResToken "(" *> absParser <* getResToken ")") <|>
    TVar <$> getVar <|> TName <$> getName

inputParser :: Parser ([(String, StrTerm)], StrTerm)
inputParser = do
    skipSpace
    binds <- many $ do
        n <- getName
        getResToken "="
        t <- absParser
        getResToken ","
        return (n, t)
    (,) binds <$> absParser <* endOfInput

natParser :: Parser Int
natParser =
    (read . BS.unpack <$> AP.takeWhile1 AP.isDigit) <|> return 0 <* skipSpace

opParser :: Parser Operation
opParser =
    skipSpace *>
    ((getResToken "#" >> OpReduction <$> natParser) <|>
    (getResToken "!" >> OpExpand <$> natParser) <|>
    OpUndo <$ getResToken "u" <|>
    OpRedo <$ getResToken "r" <|>
    OpQuit <$ getResToken "q" <|>
    OpHelp <$ getResToken "h" <|>
    return OpNull)
    <* endOfInput

-- pretty printer

padding :: [a] -> [a] -> [a]
padding _ [] = []
padding [] ys = ys
padding (x : xs) (y : ys) = x : padding xs ys

paddingh :: Int -> String -> String
paddingh n s = padding s $ replicate n ' '

paddingv :: ([String], String, [String]) -> ([String], String, [String]) ->
    ([String], String, [String], [String], String, [String])
paddingv (names1, term1, redex1) (names2, term2, redex2) =
    let nn = max (length names1) (length names2)
        rn = max (length redex1) (length redex2)
        sp n t = replicate n (map (const ' ') t) in
    (padding names1 (sp nn term1), term1, padding redex1 (sp rn term1),
     padding names2 (sp nn term2), term2, padding redex2 (sp rn term2))

absPpr, appPpr, factorPpr :: StrTerm' ->
    State (Int, Int) ([String], String, [String])

absPpr t@(TAbs _ _) = do
    let (vs, t') = destructAbs t
        pStr = "\\" ++ unwords (map (\(s, n) -> s ++ show n) vs) ++ ". "
    (names, term, redex) <- appPpr t'
    return (map (map (const ' ') pStr ++) names,
        pStr ++ term, map (map (const ' ') pStr ++) redex)
    where
    destructAbs (TAbs v t) =
        let (vs, t') = destructAbs t in (v : vs, t')
    destructAbs t = ([], t)
absPpr t = appPpr t

appPpr (TApp t1@(TAbs _ _) t2) = do
    nstr <- gets (show . snd)
    modify (second succ)
    (names1, term1, redex1, names2, term2, redex2) <-
        liftM2 paddingv (factorPpr t1) (factorPpr t2)
    let n = max (length nstr + 4) (length (term1 ++ term2) + 1)
        f (_ : xs) = '|' : xs
        f [] = []
        g = reverse . f . reverse
        spaces = replicate (n - length (term1 ++ term2)) ' '
        dashes = n - length nstr - 2
    return (
        zipWith (\n1 n2 -> n1 ++ spaces ++ n2) names1 names2,
        term1 ++ spaces ++ term2,
        zipWith (\r1 r2 -> f r1 ++ spaces ++ g r2) redex1 redex2 ++
            ["+" ++ replicate (div dashes 2) '-' ++ nstr ++
                replicate (dashes - div dashes 2) '-' ++ "+"])
appPpr (TApp t1 t2) = do
    (names1, term1, redex1, names2, term2, redex2) <-
        liftM2 paddingv (appPpr t1) (factorPpr t2)
    return (zipWith (\x y -> x ++ " " ++ y) names1 names2,
        term1 ++ " " ++ term2,
        zipWith (\x y -> x ++ " " ++ y) redex1 redex2)
appPpr t = factorPpr t

factorPpr (TName name) = do
    nstr <- gets (show . fst)
    modify (first succ)
    let n = maximum [length name, length nstr, 1]
    return ([paddingh n nstr], paddingh n name, [])
factorPpr (TVar (v, n)) = return ([], v ++ show n, [])
factorPpr (TUVar v) = return ([], v, [])
factorPpr t = do
    (names, term, redex) <- absPpr t
    let f s = " " ++ s ++ " "
    return (map f names, "(" ++ term ++ ")", map f redex)

putTerm :: StrTerm' -> IO ()
putTerm t =
    let (binds, term, redex) = evalState (absPpr t) (0, 0) in
    mapM_ (putStrLn . ("< " ++) . reverse . dropWhile (' ' ==) . reverse)
        (binds ++ [term] ++ redex)

-- main

parse' :: Parser a -> BS.ByteString -> Result a
parse' p s = feed (parse p s) BS.empty

getOpepation :: IO (Result Operation)
getOpepation = do
    eof <- isEOF
    if eof
        then return $ Done BS.empty OpQuit
        else parse' opParser <$> BS.getLine

prompt :: Map.Map String StrTerm -> History -> IO ()
prompt env history@(old, current, new) = do
    putStrLn ""
    putTerm $ fst current
    putStr "lambda>" >> hFlush stdout
    op <- getOpepation
    case op of
        Done _ (OpReduction n) ->
            case drop n (reduction (fst current)) of
                term : _ -> prompt env (current : old, (term, snd current), [])
                [] -> do
                    putStrLn "Error: Specified beta-redex is not found."
                    prompt env history
        Done _ (OpExpand n) ->
            case drop n (expand env current) of
                state : _ -> prompt env (current : old, state, [])
                [] -> do
                    putStrLn "Error: Specified subterm is not found."
                    prompt env history
        Done _ OpUndo ->
            case old of
                o : os -> prompt env (os, o, current : new)
                [] -> prompt env history
        Done _ OpRedo ->
            case new of
                n : ns -> prompt env (current : old, n, ns)
                [] -> prompt env history
        Done _ OpQuit -> return ()
        Done _ OpHelp -> do
            mapM_ putStrLn
                ["#<number>: reduce specified beta-redex",
                 "!<number>: expand specified subterm",
                 "#:         same as \"#0\"",
                 "!:         same as \"!0\"",
                 "u:         undo",
                 "r:         redo",
                 "q:         quit",
                 "h:         help"]
            prompt env history
        Done _ OpNull -> prompt env history
        err -> do
            print err
            prompt env history

main :: IO ()
main = do
    mapM_ putStrLn
        ["A Beta-Reducer  input \"h\" for help"]
    args <- getArgs
    case args of
        [] -> return ()
        file : _ -> do
            contents <- BS.readFile file
            case parse' inputParser contents of
                Done _ (binds, term) | validate binds term ->
                    prompt (Map.fromList binds)
                        ([], runState (alpha term) Map.empty, [])
                Done _ result -> putStrLn "invalid input."
                err -> print err

