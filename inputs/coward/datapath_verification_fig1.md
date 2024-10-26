# Datapath Verification Example

In SMT, the two expressions that we want to prove the equivalence of look like this:


### Specification

```.v
assign D = A << M;   // D: 31 bit
assign E = B << N ;  // E: 31 bit
assign O = D * E;
```


```
output O : bv<63> = mul(zext(logical_shift_left(zext(A, 15), zext(M, 27)), 32), zext(logical_shift_left(zext(B, 15), zext(N, 27)), 32))
```


### Implementation

```.v
assign C = A * B;   // C: 32 bit
assign P = M + N;   // P:  5 bit
assign O = C << P;
```


```
output O : bv<63> = logical_shift_left(zext(mul(zext(A, 16), zext(B, 16)), 31), zext(add(zext(M, 1), zext(N, 1)), 58))
```


## Observations

ROVER's representation essentially incorporates the `zext` (or `sext`) into the binary operation.
That seems like a win for arithmetic rewrites!
