-- The Unit type

data Unit = { MkUnit }



-- The Bool type

data Bool = { True | False }



-- The Pair type

data Pair a b = { MkPair a b }



-- The Maybe type

data Maybe a = { Nothing | Just a }



-- The Either type

data Either a b = { Left a | Right b }



-- The List type

data List a = { Nil | Cons a (List a) }



-- Function utils

id : forall a. a -> a {
  id x = x
}

const : forall a b. a -> b -> a {
  const x _ = x
}

flip : forall a b c. (a -> b -> c) -> b -> a -> c {
  flip f x y = f y x
}

applyTo : forall a b. a -> (a -> b) -> b {
  applyTo x f = f x
}

compose : forall a b c. (b -> c) -> (a -> b) -> a -> c {
  compose f g x = f (g x)
}

compose2 : forall a b c d. (c -> d) -> (a -> b -> c) -> a -> b -> d {
  compose2 f g x y = f (g x y)
}



-- Pair utils

fst : forall a b. Pair a b -> a {
  fst (MkPair x _) = x
}

snd : forall a b. Pair a b -> b {
  snd (MkPair _ y) = y
}

curry : forall a b c. (Pair a b -> c) -> a -> b -> c {
  curry f x y = f (MkPair x y)
}

uncurry : forall a b c. (a -> b -> c) -> Pair a b -> c {
  uncurry f (MkPair x y) = f x y
}

swap : forall a b. Pair a b -> Pair b a {
  swap (MkPair x y) = MkPair y x
}



-- Bool utils

and : Bool -> Bool -> Bool {
  and True True = True ;
  and True False = False ;
  and False _ = False
}

or : Bool -> Bool -> Bool {
  or False False = False ;
  or False True = True ;
  or True _ = True
}

not : Bool -> Bool {
  not True = False ;
  not False = True
}

bool : forall a. a -> a -> Bool -> a {
  bool f _ False = f ;
  bool _ t True = t
}



-- Some Int builtins

lessThanEqualsInt : Int -> Int -> Bool {
  lessThanEqualsInt x y = not (!lessThanInt y x)
}

maxInt : Int -> Int -> Int {
  maxInt x y =
    case !lessThanInt x y of {
      True -> y ;
      False -> x
    }
}

minInt : Int -> Int -> Int {
  minInt x y =
    case !lessThanInt x y of {
      True -> x ;
      False -> y
    }
}



-- Some Float builtins

lessThanEqualsFloat : Float -> Float -> Bool {
  lessThanEqualsFloat x y = not (!lessThanFloat y x)
}

maxFloat : Float -> Float -> Float {
  maxFloat x y =
    case !lessThanFloat x y of {
      True -> y ;
      False -> x
    }
}

minFloat : Float -> Float -> Float {
  minFloat x y =
    case !lessThanFloat x y of {
      True -> x ;
      False -> y
    }
}



-- List utils

append : forall a. List a -> List a -> List a {
  append Nil ys = ys ;
  append (Cons x xs) ys = Cons x (append xs ys)
}

head : forall a. List a -> Maybe a {
  head Nil = Nothing ;
  head (Cons x _) = Just x
}

last : forall a. List a -> Maybe a {
  last Nil = Nothing ;
  last (Cons x Nil) = Just x ;
  last (Cons _ (Cons x xs)) = last (Cons x xs)
}

tail : forall a. List a -> Maybe (List a) {
  tail Nil = Nothing ;
  tail (Cons _ xs) = Just xs
}

init : forall a. List a -> Maybe (List a) {
  init Nil = Nothing ;
  init (Cons x xs) =
    case init xs of {
      Nothing -> Just Nil ;
      Just ys -> Just (Cons x ys)
    }
}

uncons : forall a. List a -> Maybe (Pair a (List a)) {
  uncons Nil = Nothing ;
  uncons (Cons x xs) = Just (MkPair x xs)
}

null : forall a. List a -> Bool {
  null Nil = True ;
  null (Cons _ _) = False
}

length : forall a. List a -> Int {
  length Nil = 0 ;
  length (Cons _ xs) = !addInt 1 (length xs)
}

take : forall a. Int -> List a -> List a {
  take n xs =
    case !equalsInt n 0 of {
      True -> Nil ;
      False -> case xs of {
        Nil -> Nil ;
        Cons x xs -> Cons x (take (!subtractInt n 1) xs)
      }
    }
}

drop : forall a. Int -> List a -> List a {
  drop n xs =
    case !equalsInt n 0 of {
      True -> xs ;
      False -> case xs of {
        Nil -> Nil ;
        Cons x xs -> drop (!subtractInt n 1) xs
      }
    }
}

splitAt : forall a. Int -> List a -> Pair (List a) (List a) {
splitAt n xs =
  case !equalsInt n 0 of {
    True -> MkPair Nil xs ;
    False -> case xs of {
      Nil -> MkPair Nil Nil ;
      Cons x xs -> case splitAt (!subtractInt n 1) xs of {
        MkPair ys zs -> MkPair (Cons x ys) zs
      }
    }
  }
}

takeWhile : forall a. (a -> Bool) -> List a -> List a {
  takeWhile _ Nil = Nil ;
  takeWhile p (Cons x xs) =
    case p x of {
      True -> Cons x (takeWhile p xs) ;
      False -> Nil
    }
}

dropWhile : forall a. (a -> Bool) -> List a -> List a {
  dropWhile _ Nil = Nil ;
  dropWhile p (Cons x xs) =
    case p x of {
      True -> dropWhile p xs ;
      False -> Cons x xs
    }
}

span : forall a. (a -> Bool) -> List a -> Pair (List a) (List a) {
  span _ Nil = MkPair Nil Nil ;
  span p (Cons x xs) =
    case p x of {
      True -> case span p xs of {
        MkPair ys zs -> MkPair (Cons x ys) zs
      } ;
      False -> MkPair Nil (Cons x xs)
    }
}

groupBy : forall a. (a -> a -> Bool) -> List a -> List (List a) {
  groupBy _ Nil = Nil ;
  groupBy eq (Cons x xs) =
    case span (eq x) xs of {
      MkPair ys zs -> Cons (Cons x ys) (groupBy eq zs)
    }
}

foldr : forall a b. (a -> b -> b) -> b -> List a -> b {
  foldr _ n Nil = n ;
  foldr c n (Cons x xs) = c x (foldr c n xs)
}

foldr1 : forall a. (a -> a -> a) -> List a -> a {
  foldr1 c (Cons x Nil) = x ;
  foldr1 c (Cons x (Cons x' xs)) = c x (foldr1 c (Cons x' xs))
}

foldl : forall a b. (b -> a -> b) -> b -> List a -> b {
  foldl s n Nil = n ;
  foldl s n (Cons x xs) = foldl s (s n x) xs
}

foldl1 : forall a. (a -> a -> a) -> List a -> a {
  foldl1 s (Cons x xs) = foldl s x xs
}

unfoldr : forall a b. (b -> Maybe (Pair a b)) -> b -> List a {
  unfoldr step s =
    case step s of {
      Nothing -> Nil ;
      Just (MkPair x s') -> Cons x (unfoldr step s')
    }
}

replicate : forall a. Int -> a -> List a {
  replicate n x =
    case !equalsInt n 0 of {
      True -> Nil ;
      False -> Cons x (replicate (!subtractInt n 1) x)
    }
}

map : forall a b. (a -> b) -> List a -> List b {
  map _ Nil = Nil ;
  map f (Cons x xs) = Cons (f x) (map f xs)
}

reverseOnto : forall a. List a -> List a -> List a {
  reverseOnto Nil ys = ys ;
  reverseOnto (Cons x xs) ys = reverseOnto xs (Cons x ys)
}

reverse : forall a. List a -> List a {
  reverse xs = reverseOnto xs Nil
}

prependToAll : forall a. a -> List a -> List a {
  prependToAll sep Nil = Cons sep Nil ;
  prependToAll sep (Cons x xs) =
    Cons sep (Cons x (prependToAll sep xs))
}

intersperse : forall a. a -> List a -> List a {
  intersperse _ Nil = Nil ;
  intersperse sep (Cons x xs) = Cons x (prependToAll sep xs)
}

concat : forall a. List (List a) -> List a {
  concat Nil = Nil ;
  concat (Cons xs xss) = append xs (concat xss)
}

concatMap : forall a b. (a -> List b) -> List a -> List b {
  concatMap _ Nil = Nil ;
  concatMap f (Cons x xs) = append (f x) (concatMap f xs)
}

intercalate : forall a. List a -> List (List a) -> List a {
  intercalate xs xss = concat (intersperse xs xss)
}

filter : forall a. (a -> Bool) -> List a -> List a {
  filter _ Nil = Nil ;
  filter p (Cons x xs) =
    case p x of {
      False -> filter p xs ;
      True -> Cons x (filter p xs)
    }
}

find : forall a. (a -> Bool) -> List a -> Maybe a {
  find _ Nil = Nothing ;
  find p (Cons x xs) =
    case p x of {
      True -> Just x ;
      False -> find p xs
    }
}

partition : forall a. (a -> Bool) -> List a -> Pair (List a) (List a) {
  partition _ Nil = MkPair Nil Nil ;
  partition p (Cons x xs) =
    case partition p xs of {
      MkPair ts fs -> case p x of {
        True -> MkPair (Cons x ts) fs ;
        False -> MkPair ts (Cons x fs)
      }
    }
}

nubBy : forall a. (a -> a -> Bool) -> List a -> List a {
  nubBy _ Nil = Nil ;
  nubBy comp (Cons x xs) =
    Cons x (filter (\y -> not (comp x y)) (nubBy comp xs))
}

zipWith : forall a b c. (a -> b -> c) -> List a -> List b -> List c {
  zipWith _ Nil _ = Nil ;
  zipWith _ (Cons _ _) Nil = Nil ;
  zipWith f (Cons x xs) (Cons y ys) =
    Cons (f x y) (zipWith f xs ys)
}

zip : forall a b. List a -> List b -> List (Pair a b) {
  zip = zipWith (\x y -> MkPair x y)
}

unzip : forall a b. List (Pair a b) -> Pair (List a) (List b) {
  unzip Nil = MkPair Nil Nil ;
  unzip (Cons (MkPair x y) xys) =
    case unzip xys of {
      MkPair xs ys -> MkPair (Cons x xs) (Cons y ys)
    }
}

andList : List Bool -> Bool {
  andList Nil = True ;
  andList (Cons b bs) = and b (andList bs)
}

orList : List Bool -> Bool {
  orList Nil = False ;
  orList (Cons b bs) = or b (orList bs)
}

any : forall a. (a -> Bool) -> List a -> Bool {
  any _ Nil = False ;
  any p (Cons x xs) =
    case p x of {
      True -> True ;
      False -> any p xs
    }
}

all : forall a. (a -> Bool) -> List a -> Bool {
  all p Nil = True ;
  all p (Cons x xs) =
    case p x of {
      False -> False ;
      True -> all p xs
    }
}

sumInt : List Int -> Int {
  sumInt = foldl (\x y -> !addInt x y) 0
}

sumFloat : List Float -> Float {
  sumFloat = foldl (\x y -> !addFloat x y) 0.0
}

productInt : List Int -> Int {
  productInt = foldl (\x y -> !multiplyInt x y) 1
}

productFloat : List Float -> Float {
  productFloat = foldl (\x y -> !multiplyFloat x y) 1.0
}

maximumBy : forall a. (a -> a -> Bool) -> List a -> a {
  maximumBy comp =
    foldl1 (\x y -> case comp x y of { True -> y ; False -> x })
}

maximumInt : List Int -> Int {
  maximumInt = foldl1 maxInt
}

maximumFloat : List Float -> Float {
  maximumFloat = foldl1 maxFloat
}

minimumBy : forall a. (a -> a -> Bool) -> List a -> a {
  minimumBy comp =
    foldl1 (\x y -> case comp x y of { True -> x ; False -> y })
}

minimumInt : List Int -> Int {
  minimumInt = foldl1 minInt
}

minimumFloat : List Float -> Float {
  minimumFloat = foldl1 minFloat
}

project : forall a. List a -> Int -> Maybe a {
  project Nil _ = Nothing ;
  project (Cons x xs) n =
    case !equalsInt n 0 of {
      True -> Just x ;
      False -> project xs (!subtractInt n 1)
    }
}

findIndex : forall a. (a -> Bool) -> List a -> Maybe Int {
  findIndex _ Nil = Nothing ;
  findIndex p (Cons x xs) =
    case p x of {
      True -> Just 0 ;
      False -> case findIndex p xs of {
        Nothing -> Nothing ;
        Just i -> Just (!addInt i 1)
      }
    }
}

findIndicesFrom : forall a. Int -> (a -> Bool) -> List a -> List Int {
  findIndicesFrom _ _ Nil = Nil ;
  findIndicesFrom i p (Cons x xs) =
    case p x of {
      True -> Cons i (findIndicesFrom (!addInt i 1) p xs) ;
      False -> findIndicesFrom (!addInt i 1) p xs
    }
}

findIndices : forall a. (a -> Bool) -> List a -> List Int {
  findIndices = findIndicesFrom 0
}

evenOddSplitFrom : forall a. Bool -> List a -> Pair (List a) (List a) {
  evenOddSplitFrom _ Nil = MkPair Nil Nil ;
  evenOddSplitFrom b (Cons x xs) = case evenOddSplitFrom (not b) xs of {
    MkPair es os -> case b of {
      True -> MkPair (Cons x es) os ;
      False -> MkPair es (Cons x os)
    }
  }
}

evenOddSplit : forall a. List a -> Pair (List a) (List a) {
  evenOddSplit = evenOddSplitFrom True
}

mergeBy : forall a. (a -> a -> Bool) -> List a -> List a -> List a {
  mergeBy _ Nil ys = ys ;
  mergeBy _ (Cons x xs) Nil = Cons x xs ;
  mergeBy comp (Cons x xs) (Cons y ys) =
    case comp x y of {
      True -> Cons x (mergeBy comp xs (Cons y ys)) ;
      False -> Cons y (mergeBy comp (Cons x xs) ys)
    }
}

mergeSortBy : forall a. (a -> a -> Bool) -> List a -> List a {
  mergeSortBy _ Nil = Nil ;
  mergeSortBy comp (Cons x xs) =
    case evenOddSplit (Cons x xs) of {
      MkPair es os ->
        mergeBy comp (mergeSortBy comp es) (mergeSortBy comp os)
    }
}

quickSortBy : forall a. (a -> a -> Bool) -> List a -> List a {
  quickSortBy _ Nil = Nil ;
  quickSortBy comp (Cons x xs) =
    case partition (comp x) xs of {
      MkPair lo hi ->
        append (quickSortBy comp lo)
               (Cons x (quickSortBy comp hi))
    }
}



-- Maybe utils

maybe : forall a b. b -> (a -> b) -> Maybe a -> b {
  maybe n _ Nothing = n ;
  maybe _ j (Just x) = j x
}

isJust : forall a. Maybe a -> Bool {
  isJust (Just _) = True ;
  isJust Nothing = False
}

isNothing : forall a. Maybe a -> Bool {
  isNothing Nothing = True ;
  isNothing (Just _) = False
}

fromJust : forall a. Maybe a -> a {
  fromJust (Just x) = x
}

fromMaybe : forall a. a -> Maybe a -> a {
  fromMaybe n Nothing = n ;
  fromMaybe _ (Just x) = x
}

listToMaybe : forall a. List a -> Maybe a {
  listToMaybe Nil = Nothing ;
  listToMaybe (Cons x _) = Just x
}

maybeToList : forall a. Maybe a -> List a {
  maybeToList Nothing = Nil ;
  maybeToList (Just x) = Cons x Nil
}

catMaybes : forall a. List (Maybe a) -> List a {
  catMaybes Nil = Nil ;
  catMaybes (Cons Nothing xs) = catMaybes xs ;
  catMaybes (Cons (Just x) xs) = Cons x (catMaybes xs)
}

mapMaybe : forall a b. (a -> Maybe b) -> List a -> List b {
  mapMaybe _ Nil = Nil ;
  mapMaybe f (Cons x xs) =
    case f x of {
      Nothing -> mapMaybe f xs ;
      Just y -> Cons y (mapMaybe f xs)
    }
}



-- Either utils

either : forall a b c. (a -> c) -> (b -> c) -> Either a b -> c {
  either f _ (Left x) = f x ;
  either _ g (Right y) = g y
}

lefts : forall a b. List (Either a b) -> List a {
  lefts Nil = Nil ;
  lefts (Cons (Left x) es) = Cons x (lefts es) ;
  lefts (Cons (Right _) es) = lefts es
}

rights : forall a b. List (Either a b) -> List b {
  rights Nil = Nil ;
  rights (Cons (Right y) es) = Cons y (rights es) ;
  rights (Cons (Left _) es) = rights es
}

isLeft : forall a b. Either a b -> Bool {
  isLeft (Left _) = True ;
  isLeft (Right _) = False
}

isRight : forall a b. Either a b -> Bool {
  isRight (Right _) = True ;
  isRight (Left _) = False
}

partitionEithers : forall a b. List (Either a b) -> Pair (List a) (List b) {
  partitionEithers Nil = MkPair Nil Nil ;
  partitionEithers (Cons e es) = case partitionEithers es of {
    MkPair ls rs -> case e of {
      Left x  -> MkPair (Cons x ls) rs ;
      Right y -> MkPair ls (Cons y rs)
    }
  }
}

eitherToMaybe : forall a b. Either a b -> Maybe b {
  eitherToMaybe (Left _) = Nothing ;
  eitherToMaybe (Right y) = Just y
}

maybeToEither : forall a b. a -> Maybe b -> Either a b {
  maybeToEither x Nothing = Left x ;
  maybeToEither _ (Just y) = Right y
}






-- Hashing

addressHash : ByteString -> ByteString {
  addressHash x = blake2b_224 (sha3_256 x)
}





-- Multisig verification

-- arguments:
--   * signed data
--   * hash of key
--   * key and signature
--
verifyHelper : ByteString -> ByteString -> Maybe (Pair ByteString ByteString) -> Bool {
  verifyHelper _ _ Nothing = False ;
  verifyHelper dat kh (Just (MkPair k s)) =
    and (!equalsByteString kh (addressHash k))
        (!verifySignature k dat s)
}

-- arguments:
--   * how many valid signatures are needed
--   * list of pubkey hashes that are allowed to "vote" for the transaction
--     (the hash used is 'addressHash')
--   * TxSigData
--   * list of pubkeys who have provided sigs, and corresponding sigs
--
verifyMultiSig : Int -> List ByteString -> ByteString -> List (Maybe (Pair ByteString ByteString)) -> Comp Unit {
  verifyMultiSig n keyhashes dat sigs =
    case and (!equalsInt (length keyhashes) (length sigs))
             (lessThanEqualsInt n (length (filter (\x -> x) (zipWith (verify dat) keyhashes sigs)))) of {
      True -> success MkUnit ;
      False -> failure
    }
}




-- MAST

data MASTProp =
  { MASTTrue
  | MASTFalse
  | MASTNot MASTProp
  | MASTAnd MASTProp MASTProp
  | MASTOr MASTProp MASTProp
  }

data MASTTree =
  { MASTSuccess
  | MASTFailure
  | MASTIf MASTProp MASTTree MASTTree
  }

data MASTPath =
  { MASTPathSuccess
  | MASTPathFailure
  | MASTPathIfTrue MASTProp MASTPath ByteString
  | MASTPathIfFalse MASTProp ByteString MASTPath
  }

evalMASTProp : MASTProp -> Bool {
  evalMASTProp (MASTNot x) = not (evalMASTProp x) ;
  evalMASTProp (MASTAnd x y) =
    and (evalMASTProp x) (evalMASTProp y) ;
  evalMASTProp (MASTOr x y) =
    or (evalMASTProp x) (evalMASTProp y)
}

evalMASTPath : MASTPath -> Bool {
  evalMASTPath MASTPathSuccess = True ;
  evalMASTPath MASTPathFailure = False ;
  evalMASTPath (MASTPathIfTrue test t _) =
    case evalMASTProp test of {
      True -> evalMASTPath t ;
      False -> False
    } ;
  evalMASTPath (MASTPathIfFalse test _ f) =
    case evalMASTProp test of {
      True -> False ;
      False -> evalMASTPath f
    }
}

hashMASTProp : MASTProp -> ByteString {
  hashMASTProp (MASTNot x) =
    !sha2_256
      (!concatenate
        #00
        (hashMASTProp x)) ;
  hashMASTProp (MASTAnd x y) =
    !sha2_256
      (!concatenate
        #01
        (!concatenate
          (hashMASTProp x)
          (hashMASTProp y))) ;
  hashMASTProp (MASTOr x y) =
    !sha2_256
      (!concatenate
        #02
        (!concatenate
          (hashMASTProp x)
          (hashMASTProp y)))
}

hashMASTTree : MASTTree -> ByteString {
  hashMASTTree MASTSuccess = #00 ;
  hashMASTTree MASTFailure = #01 ;
  hashMASTTree (MASTIf test t f) =
    !sha2_256
      (!concatenate
        #02
        (!concatenate
          (hashMASTTree t)
          (hashMASTTree f)))
}

hashMASTPath : MASTPath -> ByteString {
  hashMASTPath MASTPathSuccess = #00 ;
  hashMASTPath MASTPathFailure = #01 ;
  hashMASTPath (MASTPathIfTrue test t fhash) =
    !sha2_256
      (!concatenate
        #02
        (!concatenate
          (hashMASTPath t)
          fhash)) ;
  hashMASTPath (MASTPathIfFalse test thash f) =
    !sha2_256
      (!concatenate
        #02
        (!concatenate
          thash
          (hashMASTPath f)))
}

checkMAST : ByteString -> MASTPath -> Bool {
  checkMAST hash path =
    case evalMASTPath path of {
      False -> False ;
      True -> !equalsByteString hash (hashMASTPath path)
    }
}