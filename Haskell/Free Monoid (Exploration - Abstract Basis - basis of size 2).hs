#!/usr/bin/env stack
-- stack --resolver lts-20.5 ghci --package QuickCheck-2.14.2

import Data.Monoid
import Data.Foldable
import Test.QuickCheck hiding ((.&.), (.|.))
import Data.Bits

-- Define Basis2 with three elements
data Basis2 = A | B deriving (Eq, Show)

toBool A = False
toBool B = True

fromBool False = A
fromBool True  = B

-- Make Basis2 an instance of Arbitrary for QuickCheck testing
instance Arbitrary Basis2 where
    arbitrary = elements [A, B]

class Free m where
    canonicalInj :: b -> m b

instance Bits Basis2 where
    x .&. y = fromBool $ toBool x .&. toBool y 
    x .|. y = fromBool $ toBool x .|. toBool y 
    x `xor` y = fromBool $ toBool x `xor` toBool y
    complement = fromBool . complement . toBool
    shift x n = fromBool . flip shift n . toBool $ x
    rotate x n = fromBool . flip rotate n . toBool $ x
    bitSize = finiteBitSize . toBool
    bitSizeMaybe = bitSizeMaybe . toBool
    isSigned = isSigned . toBool
    testBit = testBit . toBool
    bit = fromBool . bit
    popCount = popCount . toBool

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

instance Arbitrary a => Arbitrary (Ior a) where
    arbitrary = Ior <$> arbitrary

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

    putStrLn "Testing Ior for monoid laws:"
    quickCheck (prop_leftIdentity :: Ior Basis2 -> Property)
    quickCheck (prop_rightIdentity :: Ior Basis2 -> Property)
    quickCheck (prop_associativity :: Ior Basis2 -> Ior Basis2 -> Ior Basis2 -> Property)
    putStr "\n"

    putStrLn "Testing homomorphism properties MaybeList Basis2 To Ior:"
    quickCheck (prop_identityPreservation maybeBasis2ListToIor1)
    quickCheck (prop_identityPreservation maybeBasis2ListToIor2)
    quickCheck (prop_operationPreservation maybeBasis2ListToIor1)
    quickCheck (prop_operationPreservation maybeBasis2ListToIor2)
    putStr "\n"

    putStrLn "Testing prop_universal_property_commuting for g and maybeBasis2ListToIor1"
    quickCheck (prop_universal_property_commuting g maybeBasis2ListToIor1)
    putStr "\n"

    putStrLn "Testing prop_universal_property_commuting for g and maybeBasis2ListToIor2"
    quickCheck (prop_universal_property_commuting g maybeBasis2ListToIor2)
    putStr "\n"

    putStrLn "Testing if homomorphism is non-unique:"
    quickCheck (prop_equal_on_generators maybeBasis2ListToIor1 maybeBasis2ListToIor2)
    quickCheck (prop_unique_universal_morphism maybeBasis2ListToIor1 maybeBasis2ListToIor2 :: MaybeList Basis2 -> Property)
    putStr "\n"
    putStr "\n"
  where -- g is a counter example to any g between sets Basis -> UnderlyingSetOf SomeMonoid having a unique homomorphism (where SomeMonoid = Ior)
        g :: Basis2 -> Ior Basis2
        g A = Ior B
        g B  = Ior B
        
        maybeBasis2ListToIor1 :: MaybeList Basis2 -> Ior Basis2
        maybeBasis2ListToIor1 (MaybeList Nothing  ) = Ior A
        maybeBasis2ListToIor1 (MaybeList (Just [])) = Ior A
        maybeBasis2ListToIor1 (MaybeList (Just xs)) = Ior B
        
        maybeBasis2ListToIor2 :: MaybeList Basis2 -> Ior Basis2
        maybeBasis2ListToIor2 (MaybeList Nothing  ) = Ior A
        maybeBasis2ListToIor2 (MaybeList (Just [])) = Ior B
        maybeBasis2ListToIor2 (MaybeList (Just xs)) = Ior B

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

type UnderLyingSetOfIor = Basis2
boolList_IsFree_For_Ior :: IO ()
boolList_IsFree_For_Ior = do
    putStrLn "Testing [Basis2] for monoid laws:"
    quickCheck (prop_leftIdentity :: [Basis2] -> Property)
    quickCheck (prop_rightIdentity :: [Basis2] -> Property)
    quickCheck (prop_associativity :: [Basis2] -> [Basis2] -> [Basis2] -> Property)
    putStr "\n"

    putStrLn "Testing Ior for monoid laws:"
    quickCheck (prop_leftIdentity :: Ior Basis2 -> Property)
    quickCheck (prop_rightIdentity :: Ior Basis2 -> Property)
    quickCheck (prop_associativity :: Ior Basis2 -> Ior Basis2 -> Ior Basis2 -> Property)
    putStr "\n"

    putStrLn "Testing homomorphism properties [Basis2] To Ior:"
    sequence $ [quickCheck (prop_identityPreservation boolListToIor) | boolMap <- allBasis2Maps, let testMap = Ior . boolMap, let boolListToIor = foldMap Ior . map boolMap]
    sequence $ [quickCheck (prop_operationPreservation boolListToIor) | boolMap <- allBasis2Maps, let testMap = Ior . boolMap, let boolListToIor = foldMap Ior . map boolMap]
    putStr "\n"

    putStrLn "Testing prop_universal_property_commuting"
    sequence $ [quickCheck (prop_universal_property_commuting testMap boolListToIor) | boolMap <- allBasis2Maps, let testMap = Ior . boolMap, let boolListToIor = foldMap Ior . map boolMap]
    putStr "\n"
    putStr "\n"
  where allBasis2Maps :: [Basis2 -> UnderLyingSetOfIor]
        allBasis2Maps = [fromBool . f . toBool | f <- [id, not, const True, const False]]


main = do
    maybeBasis2List_IsNotFree_Proof1
    maybeBasis2List_IsNotFree_Proof2
    boolList_IsFree_For_Ior