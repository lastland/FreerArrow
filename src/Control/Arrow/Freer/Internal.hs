module Control.Arrow.Freer.Internal where

assocsumprod :: (Either (a, b) c, d) -> Either (a, (b, d)) (c, d)
assocsumprod (Left (a, b), d) = Left (a, (b, d))
assocsumprod (Right c, d)     = Right (c, d)

unassocsumprod :: Either (a, (b, d)) (c, d) -> (Either (a, b) c, d)
unassocsumprod (Left (a, (b, d))) = (Left (a, b), d)
unassocsumprod (Right (c, d))     = (Right c, d)

assocprodsum :: Either (Either a c, w) v -> Either (a, w) (Either (c, w) v)
assocprodsum (Left (Left a, w)) = Left (a, w)
assocprodsum (Left (Right c, w)) = Right (Left (c, w))
assocprodsum (Right v) = Right (Right v)

unassocprodsum :: Either (a, w) (Either (c, w) v) -> Either (Either a c, w) v
unassocprodsum (Left (a, w)) = Left (Left a, w)
unassocprodsum (Right (Left (c, w))) = Left (Right c, w)
unassocprodsum (Right (Right v)) = Right v

assocsum :: Either (Either a b) c -> Either a (Either b c)
assocsum (Left (Left a)) = Left a
assocsum (Left (Right b)) = Right (Left b)
assocsum (Right c) = Right (Right c)

unassocsum :: Either a (Either b c) -> Either (Either a b) c
unassocsum (Left a) = Left (Left a)
unassocsum (Right (Left b)) = Left (Right b)
unassocsum (Right (Right c)) = Right c
