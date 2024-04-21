#!/usr/bin/env stack
-- stack --resolver lts-20.5 ghci --package QuickCheck-2.14.2

import Data.Monoid
import Data.Foldable
import Test.QuickCheck

-- Define Basis2 with three elements
data Basis2 = A | B deriving (Eq, Show)

toEnumBasis2 :: Int -> Basis2
toEnumBasis2 0 = A
toEnumBasis2 _ = B

fromEnumBasis2 :: Basis2 -> Int
fromEnumBasis2 A = 0
fromEnumBasis2 B = 1

toEnumMax2 :: Int -> Max2 Basis2
toEnumMax2 0 = (Max2 A)
toEnumMax2 1 = (Max2 B)

fromEnumMax2 :: Max2 Basis2 -> Int
fromEnumMax2 (Max2 A) = 0
fromEnumMax2 (Max2 B) = 1

-- Make Basis2 an instance of Arbitrary for QuickCheck testing
instance Arbitrary Basis2 where
    arbitrary = elements [A, B]

-- Define a new Monoid to replace Max2 for three elements
data Max2 a = Max2 {fromMax2 :: a} deriving (Eq, Show)

instance Semigroup (Max2 Basis2) where
    x <> y = toEnumMax2 $ max (fromEnumMax2 x) (fromEnumMax2 y)

instance Monoid (Max2 Basis2) where
    mempty = toEnumMax2 0

-- Make Max2 an instance of Arbitrary
instance Arbitrary (Max2 Basis2) where
    arbitrary = elements [Max2 A, Max2 B]

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
prop_universal_property_commuting :: (Eq a, Show a, Free f) => (Basis2 -> a) -> (f Basis2 -> a) -> Basis2 -> Property
prop_universal_property_commuting testMap homomorphism = commutesOnInput
  where commutesOnInput input = testMap input === (homomorphism . canonicalInj) input

prop_equal_on_generators :: (Eq a, Show a, Free f) => (f Basis2 -> a) -> (f Basis2 -> a) -> Basis2 -> Property
prop_equal_on_generators homomorphism1 homomorphism2 = commutesOnInput
  where commutesOnInput input = (homomorphism1 . canonicalInj) input === (homomorphism2 . canonicalInj) input

prop_unique_universal_morphism :: (Eq a, Show a) => (t -> a) -> (t -> a) -> t -> Property
prop_unique_universal_morphism morphism1 morphism2 input = (morphism1 input === morphism2 input)


----------------------------
-- (Testing for Freeness) --
----------------------------
------ MaybeList Basis2 --------
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

maybeBasis2List_IsNotFree_Proof1 :: IO ()
maybeBasis2List_IsNotFree_Proof1 = do
    putStrLn "Testing MaybeList Basis2 for monoid laws:"
    quickCheck (prop_leftIdentity :: MaybeList Basis2 -> Property)
    quickCheck (prop_rightIdentity :: MaybeList Basis2 -> Property)
    quickCheck (prop_associativity :: MaybeList Basis2 -> MaybeList Basis2 -> MaybeList Basis2 -> Property)
    putStr "\n"

    putStrLn "Testing Max2 for monoid laws:"
    quickCheck (prop_leftIdentity :: Max2 Basis2 -> Property)
    quickCheck (prop_rightIdentity :: Max2 Basis2 -> Property)
    quickCheck (prop_associativity :: Max2 Basis2 -> Max2 Basis2 -> Max2 Basis2 -> Property)
    putStr "\n"

    putStrLn "Testing homomorphism properties MaybeList Basis2 To Max2:"
    quickCheck (prop_identityPreservation maybeBasis2ListToMax2_1)
    quickCheck (prop_identityPreservation maybeBasis2ListToMax2_2)
    quickCheck (prop_operationPreservation maybeBasis2ListToMax2_1)
    quickCheck (prop_operationPreservation maybeBasis2ListToMax2_2)
    putStr "\n"

    putStrLn "Testing prop_universal_property_commuting for g and maybeBasis2ListToMax2_1"
    quickCheck (prop_universal_property_commuting g maybeBasis2ListToMax2_1)
    putStr "\n"

    putStrLn "Testing prop_universal_property_commuting for g and maybeBasis2ListToMax2_2"
    quickCheck (prop_universal_property_commuting g maybeBasis2ListToMax2_2)
    putStr "\n"

    putStrLn "Testing if homomorphism is non-unique:"
    quickCheck (prop_equal_on_generators maybeBasis2ListToMax2_1 maybeBasis2ListToMax2_2)
    quickCheck (prop_unique_universal_morphism maybeBasis2ListToMax2_1 maybeBasis2ListToMax2_2 :: MaybeList Basis2 -> Property)
    putStr "\n"
    putStr "\n"
  where -- g is a counter example to any g between sets Basis -> UnderlyingSetOf SomeMonoid having a unique homomorphism (where SomeMonoid = Max2)
        g :: Basis2 -> Max2 Basis2
        g A = Max2 B
        g B = Max2 B
        
        maybeBasis2ListToMax2_1 :: MaybeList Basis2 -> Max2 Basis2
        maybeBasis2ListToMax2_1 (MaybeList Nothing  ) = Max2 A
        maybeBasis2ListToMax2_1 (MaybeList (Just [])) = Max2 A
        maybeBasis2ListToMax2_1 (MaybeList (Just xs)) = Max2 B
        
        maybeBasis2ListToMax2_2 :: MaybeList Basis2 -> Max2 Basis2
        maybeBasis2ListToMax2_2 (MaybeList Nothing  ) = Max2 A
        maybeBasis2ListToMax2_2 (MaybeList (Just [])) = Max2 B
        maybeBasis2ListToMax2_2 (MaybeList (Just xs)) = Max2 B

maybeBasis2List_IsNotFree_Proof2 :: IO ()
maybeBasis2List_IsNotFree_Proof2 = do
    putStrLn "Testing MaybeList Basis2 for monoid laws:"
    quickCheck (prop_leftIdentity :: MaybeList Basis2 -> Property)
    quickCheck (prop_rightIdentity :: MaybeList Basis2 -> Property)
    quickCheck (prop_associativity :: MaybeList Basis2 -> MaybeList Basis2 -> MaybeList Basis2 -> Property)
    putStr "\n"
    
    putStrLn "Testing MaybeList Basis2 for monoid laws:"
    quickCheck (prop_leftIdentity :: MaybeList Basis2 -> Property)
    quickCheck (prop_rightIdentity :: MaybeList Basis2 -> Property)
    quickCheck (prop_associativity :: MaybeList Basis2 -> MaybeList Basis2 -> MaybeList Basis2 -> Property)
    putStr "\n"

    putStrLn "Testing homomorphism properties MaybeList Basis2 To MaybeList Basis2:"
    quickCheck (prop_identityPreservation maybeBasis2ListToMaybeBasis2List1)
    quickCheck (prop_identityPreservation maybeBasis2ListToMaybeBasis2List2)
    quickCheck (prop_operationPreservation maybeBasis2ListToMaybeBasis2List1)
    quickCheck (prop_operationPreservation maybeBasis2ListToMaybeBasis2List2)
    putStr "\n"

    putStrLn "Testing prop_universal_property_commuting for testMap1 and maybeBasis2ListToMaybeBasis2List1"
    quickCheck (prop_universal_property_commuting testMap1 maybeBasis2ListToMaybeBasis2List1)
    putStr "\n"

    putStrLn "Testing prop_universal_property_commuting for testMap1 and maybeBasis2ListToMaybeBasis2List2"
    quickCheck (prop_universal_property_commuting testMap1 maybeBasis2ListToMaybeBasis2List2)
    putStr "\n"

    putStrLn "Testing if homomorphism is non-unique:"
    quickCheck (prop_equal_on_generators maybeBasis2ListToMaybeBasis2List1 maybeBasis2ListToMaybeBasis2List2)
    quickCheck (prop_unique_universal_morphism maybeBasis2ListToMaybeBasis2List1 maybeBasis2ListToMaybeBasis2List2 :: MaybeList Basis2 -> Property)
    putStr "\n"
    putStr "\n"
  where testMap1 :: Basis2 -> MaybeList Basis2
        testMap1 A = MaybeList (Just [A])
        testMap1 B  = MaybeList (Just [B])
        
        maybeBasis2ListToMaybeBasis2List1 :: MaybeList Basis2 -> MaybeList Basis2
        maybeBasis2ListToMaybeBasis2List1 (MaybeList Nothing  ) = MaybeList (Nothing)
        maybeBasis2ListToMaybeBasis2List1 (MaybeList (Just [])) = MaybeList (Nothing)
        maybeBasis2ListToMaybeBasis2List1 (MaybeList (Just xs)) = MaybeList (Just xs)

        maybeBasis2ListToMaybeBasis2List2 :: MaybeList Basis2 -> MaybeList Basis2
        maybeBasis2ListToMaybeBasis2List2 (MaybeList Nothing  ) = MaybeList (Nothing)
        maybeBasis2ListToMaybeBasis2List2 (MaybeList (Just [])) = MaybeList (Just [])
        maybeBasis2ListToMaybeBasis2List2 (MaybeList (Just xs)) = MaybeList (Just xs)


----------------------------
-- (Testing for Freeness) --
----------------------------
--------- [Basis2] -----------
----------------------------

instance Free [] where
    canonicalInj = (:[])

type UnderLyingSetOfMax2 = Basis2
basis3List_IsFree_For_Max2 :: IO ()
basis3List_IsFree_For_Max2 = do
    putStrLn "Testing [Basis2] for monoid laws:"
    quickCheck (prop_leftIdentity :: [Basis2] -> Property)
    quickCheck (prop_rightIdentity :: [Basis2] -> Property)
    quickCheck (prop_associativity :: [Basis2] -> [Basis2] -> [Basis2] -> Property)
    putStr "\n"

    putStrLn "Testing Max2 for monoid laws:"
    quickCheck (prop_leftIdentity :: Max2 Basis2 -> Property)
    quickCheck (prop_rightIdentity :: Max2 Basis2 -> Property)
    quickCheck (prop_associativity :: Max2 Basis2 -> Max2 Basis2 -> Max2 Basis2 -> Property)
    putStr "\n"

    putStrLn "Testing homomorphism properties [Basis2] To Max2:"
    sequence $ [quickCheck (prop_identityPreservation basis3ListToMax2) | triMap <- allBasis2Maps, let testMap = Max2 . triMap, let basis3ListToMax2 = foldMap Max2 . map triMap]
    sequence $ [quickCheck (prop_operationPreservation basis3ListToMax2) | triMap <- allBasis2Maps, let testMap = Max2 . triMap, let basis3ListToMax2 = foldMap Max2 . map triMap]
    putStr "\n"

    putStrLn "Testing prop_universal_property_commuting"
    sequence $ [quickCheck (prop_universal_property_commuting testMap basis3ListToMax2) | triMap <- allBasis2Maps, let testMap = Max2 . triMap, let basis3ListToMax2 = foldMap Max2 . map triMap]
    putStr "\n"
    putStr "\n"
  where allBasis2Maps :: [Basis2 -> UnderLyingSetOfMax2]
        allBasis2Maps = [f x y z | [x,y,z] <- sequence (replicate 3 [A,B])]
        
        f x y z = func
          where func A = x
                func B = y

main = do
    maybeBasis2List_IsNotFree_Proof1
    maybeBasis2List_IsNotFree_Proof2
    basis3List_IsFree_For_Max2