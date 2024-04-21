#!/usr/bin/env stack
-- stack --resolver lts-20.5 ghci --package QuickCheck-2.14.2

import Data.Monoid
import Data.Foldable
import Test.QuickCheck

-- Define BasisN with three elements
data BasisN = BasisN {fromBasisN :: Int} deriving (Eq, Show)

instance Ord BasisN where
  BasisN n <= BasisN 1 = True
  BasisN 1 <= BasisN m = False
  BasisN n <= BasisN m = n <= m

toEnumBasisN :: Int -> BasisN
toEnumBasisN = BasisN

fromEnumBasisN :: BasisN -> Int
fromEnumBasisN = fromBasisN

toEnumMaxN :: Int -> MaxN BasisN
toEnumMaxN n = (MaxN (BasisN n))

fromEnumMaxN :: MaxN BasisN -> Int
fromEnumMaxN (MaxN (BasisN n)) = n

-- Make BasisN an instance of Arbitrary for QuickCheck testing
instance Arbitrary BasisN where
    arbitrary = BasisN . getNonNegative <$> arbitrary

-- Define a new Monoid to replace MaxN for three elements
data MaxN a = MaxN {fromMaxN :: a} deriving (Eq, Show)

instance Semigroup (MaxN BasisN) where
    MaxN x <> MaxN y = MaxN $ max x y

instance Monoid (MaxN BasisN) where
    mempty = toEnumMaxN 0

-- Make MaxN an instance of Arbitrary
instance Arbitrary (MaxN BasisN) where
    arbitrary = MaxN <$> arbitrary

class Free m where
    canonicalInj :: b -> m b

-- Monoid properties
-- Left Identity
prop_leftIdentity :: (Eq m, Monoid m, Show m) => m -> Property
prop_leftIdentity x = mempty <> x === x

-- Right Identity
prop_rightIdentity :: (Eq m, Monoid m, Show m) => m -> Property
prop_rightIdentity x = x <> mempty === x

-- Associativity
prop_associativity :: (Eq m, Monoid m, Show m) => m -> m -> m -> Property
prop_associativity x y z = (x <> y) <> z === x <> (y <> z)


-- Homomorphism Properties
-- Identity Preservation Property
prop_identityPreservation :: (Monoid a, Monoid b, Eq b, Show b) => (a -> b) -> Property
prop_identityPreservation homomorphism =
  homomorphism mempty === mempty

-- Operation Preservation Property
prop_operationPreservation :: (Monoid a, Monoid b, Eq b, Show b) => (a -> b) -> a -> a -> Property
prop_operationPreservation homomorphism x y =
  homomorphism (x <> y) === (homomorphism x <> homomorphism y)

-- Universal Property (Commuting triangle)
prop_universal_property_commuting :: (Eq a, Show a, Free f) => (BasisN -> a) -> (f BasisN -> a) -> BasisN -> Property
prop_universal_property_commuting testMap homomorphism = commutesOnInput
  where commutesOnInput input = testMap input === (homomorphism . canonicalInj) input

prop_equal_on_generators :: (Eq a, Show a, Free f) => (f BasisN -> a) -> (f BasisN -> a) -> BasisN -> Property
prop_equal_on_generators homomorphism1 homomorphism2 = commutesOnInput
  where commutesOnInput input = (homomorphism1 . canonicalInj) input === (homomorphism2 . canonicalInj) input

prop_unique_universal_morphism :: (Eq a, Show a) => (t -> a) -> (t -> a) -> t -> Property
prop_unique_universal_morphism morphism1 morphism2 input = (morphism1 input === morphism2 input)


----------------------------
-- (Testing for Freeness) --
----------------------------
------ MaybeList BasisN --------
----------------------------
newtype MaybeList a = MaybeList {fromMaybeList :: Maybe [a]} deriving (Show, Eq)
instance Free MaybeList where
    canonicalInj = MaybeList . Just . (:[])

instance Arbitrary a => Arbitrary (MaybeList a) where
    arbitrary = MaybeList <$> arbitrary

instance Semigroup (MaybeList a) where
    (MaybeList x) <> (MaybeList y) = MaybeList (x <> y)

instance Monoid (MaybeList a) where
    mempty = MaybeList mempty

maybeBasisNList_IsNotFree_Proof1 :: IO ()
maybeBasisNList_IsNotFree_Proof1 = do
    putStrLn "Testing MaybeList BasisN for monoid laws:"
    quickCheck (prop_leftIdentity :: MaybeList BasisN -> Property)
    quickCheck (prop_rightIdentity :: MaybeList BasisN -> Property)
    quickCheck (prop_associativity :: MaybeList BasisN -> MaybeList BasisN -> MaybeList BasisN -> Property)
    putStr "\n"

    putStrLn "Testing MaxN for monoid laws:"
    quickCheck (prop_leftIdentity :: MaxN BasisN -> Property)
    quickCheck (prop_rightIdentity :: MaxN BasisN -> Property)
    quickCheck (prop_associativity :: MaxN BasisN -> MaxN BasisN -> MaxN BasisN -> Property)
    putStr "\n"

    putStrLn "Testing homomorphism properties MaybeList BasisN To MaxN:"
    quickCheck (prop_identityPreservation maybeBasisNListToMaxN_1)
    quickCheck (prop_identityPreservation maybeBasisNListToMaxN_2)
    quickCheck (prop_operationPreservation maybeBasisNListToMaxN_1)
    quickCheck (prop_operationPreservation maybeBasisNListToMaxN_2)
    putStr "\n"

    putStrLn "Testing prop_universal_property_commuting for g and maybeBasisNListToMaxN_1"
    quickCheck (prop_universal_property_commuting g maybeBasisNListToMaxN_1)
    putStr "\n"

    putStrLn "Testing prop_universal_property_commuting for g and maybeBasisNListToMaxN_2"
    quickCheck (prop_universal_property_commuting g maybeBasisNListToMaxN_2)
    putStr "\n"

    putStrLn "Testing if homomorphism is non-unique:"
    quickCheck (prop_equal_on_generators maybeBasisNListToMaxN_1 maybeBasisNListToMaxN_2)
    quickCheck (prop_unique_universal_morphism maybeBasisNListToMaxN_1 maybeBasisNListToMaxN_2 :: MaybeList BasisN -> Property)
    putStr "\n"
    putStr "\n"
  where -- g is a counter example to any g between sets Basis -> UnderlyingSetOf SomeMonoid having a unique homomorphism (where SomeMonoid = MaxN)
        g :: BasisN -> MaxN BasisN
        g (BasisN 0) = MaxN (BasisN 1)
        g (BasisN n) = MaxN (BasisN 1)
        
        maybeBasisNListToMaxN_1 :: MaybeList BasisN -> MaxN BasisN
        maybeBasisNListToMaxN_1 (MaybeList Nothing  ) = MaxN (BasisN 0)
        maybeBasisNListToMaxN_1 (MaybeList (Just [])) = MaxN (BasisN 0)
        maybeBasisNListToMaxN_1 (MaybeList (Just xs)) = MaxN (BasisN 1)
        
        maybeBasisNListToMaxN_2 :: MaybeList BasisN -> MaxN BasisN
        maybeBasisNListToMaxN_2 (MaybeList Nothing  ) = MaxN (BasisN 0)
        maybeBasisNListToMaxN_2 (MaybeList (Just [])) = MaxN (BasisN 1)
        maybeBasisNListToMaxN_2 (MaybeList (Just xs)) = MaxN (BasisN 1)

maybeBasisNList_IsNotFree_Proof2 :: IO ()
maybeBasisNList_IsNotFree_Proof2 = do
    putStrLn "Testing MaybeList BasisN for monoid laws:"
    quickCheck (prop_leftIdentity :: MaybeList BasisN -> Property)
    quickCheck (prop_rightIdentity :: MaybeList BasisN -> Property)
    quickCheck (prop_associativity :: MaybeList BasisN -> MaybeList BasisN -> MaybeList BasisN -> Property)
    putStr "\n"
    
    putStrLn "Testing MaybeList BasisN for monoid laws:"
    quickCheck (prop_leftIdentity :: MaybeList BasisN -> Property)
    quickCheck (prop_rightIdentity :: MaybeList BasisN -> Property)
    quickCheck (prop_associativity :: MaybeList BasisN -> MaybeList BasisN -> MaybeList BasisN -> Property)
    putStr "\n"

    putStrLn "Testing homomorphism properties MaybeList BasisN To MaybeList BasisN:"
    quickCheck (prop_identityPreservation maybeBasisNListToMaybeBasisNList1)
    quickCheck (prop_identityPreservation maybeBasisNListToMaybeBasisNList2)
    quickCheck (prop_operationPreservation maybeBasisNListToMaybeBasisNList1)
    quickCheck (prop_operationPreservation maybeBasisNListToMaybeBasisNList2)
    putStr "\n"

    putStrLn "Testing prop_universal_property_commuting for testMap1 and maybeBasisNListToMaybeBasisNList1"
    quickCheck (prop_universal_property_commuting testMap1 maybeBasisNListToMaybeBasisNList1)
    putStr "\n"

    putStrLn "Testing prop_universal_property_commuting for testMap1 and maybeBasisNListToMaybeBasisNList2"
    quickCheck (prop_universal_property_commuting testMap1 maybeBasisNListToMaybeBasisNList2)
    putStr "\n"

    putStrLn "Testing if homomorphism is non-unique:"
    quickCheck (prop_equal_on_generators maybeBasisNListToMaybeBasisNList1 maybeBasisNListToMaybeBasisNList2)
    quickCheck (prop_unique_universal_morphism maybeBasisNListToMaybeBasisNList1 maybeBasisNListToMaybeBasisNList2 :: MaybeList BasisN -> Property)
    putStr "\n"
    putStr "\n"
  where testMap1 :: BasisN -> MaybeList BasisN
        testMap1 (BasisN 0) = MaybeList (Just [BasisN 0])
        testMap1 (BasisN n) = MaybeList (Just [BasisN n])
        
        maybeBasisNListToMaybeBasisNList1 :: MaybeList BasisN -> MaybeList BasisN
        maybeBasisNListToMaybeBasisNList1 (MaybeList Nothing  ) = MaybeList (Nothing)
        maybeBasisNListToMaybeBasisNList1 (MaybeList (Just [])) = MaybeList (Nothing)
        maybeBasisNListToMaybeBasisNList1 (MaybeList (Just xs)) = MaybeList (Just xs)

        maybeBasisNListToMaybeBasisNList2 :: MaybeList BasisN -> MaybeList BasisN
        maybeBasisNListToMaybeBasisNList2 (MaybeList Nothing  ) = MaybeList (Nothing)
        maybeBasisNListToMaybeBasisNList2 (MaybeList (Just [])) = MaybeList (Just [])
        maybeBasisNListToMaybeBasisNList2 (MaybeList (Just xs)) = MaybeList (Just xs)


----------------------------
-- (Testing for Freeness) --
----------------------------
--------- [BasisN] -----------
----------------------------

instance Free [] where
    canonicalInj = (:[])

type UnderLyingSetOfMaxN = BasisN
basis3List_IsFree_For_MaxN :: IO ()
basis3List_IsFree_For_MaxN = do
    putStrLn "Testing [BasisN] for monoid laws:"
    quickCheck (prop_leftIdentity :: [BasisN] -> Property)
    quickCheck (prop_rightIdentity :: [BasisN] -> Property)
    quickCheck (prop_associativity :: [BasisN] -> [BasisN] -> [BasisN] -> Property)
    putStr "\n"

    putStrLn "Testing MaxN for monoid laws:"
    quickCheck (prop_leftIdentity :: MaxN BasisN -> Property)
    quickCheck (prop_rightIdentity :: MaxN BasisN -> Property)
    quickCheck (prop_associativity :: MaxN BasisN -> MaxN BasisN -> MaxN BasisN -> Property)
    putStr "\n"

    putStrLn "Testing homomorphism properties [BasisN] To MaxN:"
    sequence $ [quickCheck (prop_identityPreservation basis3ListToMaxN) | triMap <- allBasisNMaps, let testMap = MaxN . triMap, let basis3ListToMaxN = foldMap MaxN . map triMap]
    sequence $ [quickCheck (prop_operationPreservation basis3ListToMaxN) | triMap <- allBasisNMaps, let testMap = MaxN . triMap, let basis3ListToMaxN = foldMap MaxN . map triMap]
    putStr "\n"

    putStrLn "Testing prop_universal_property_commuting"
    sequence $ [quickCheck (prop_universal_property_commuting testMap basis3ListToMaxN) | triMap <- allBasisNMaps, let testMap = MaxN . triMap, let basis3ListToMaxN = foldMap MaxN . map triMap]
    putStr "\n"
    putStr "\n"
  where allBasisNMaps :: [BasisN -> UnderLyingSetOfMaxN]
        allBasisNMaps = [f ys | let n = 4, ys <- sequence (replicate n [1..n])] -- n = 4 but should be infinite to allow for arbitrary basis size
        
        f ys (BasisN n)
            | n < length ys = BasisN (ys !! n)
            | otherwise     = BasisN 1

main = do
    maybeBasisNList_IsNotFree_Proof1
    maybeBasisNList_IsNotFree_Proof2
    basis3List_IsFree_For_MaxN