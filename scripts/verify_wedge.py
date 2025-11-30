#!/usr/bin/env python3
"""
Verify the wedge closure inequality:
    Upsilon = (C_geom * sqrt(K_xi)) / (pi * c_plateau) < 0.5

Edit the constants below to audit different locked values.
"""
import math

# Locked example constants (see riemann-boundary-certificate.tex, Table of Constants)
C_geom = 0.24       # geometric window/tent constant
c_plateau = 0.1762  # Poisson plateau constant
K_xi = 0.16         # assembled box-energy constant

Upsilon = (C_geom * math.sqrt(K_xi)) / (math.pi * c_plateau)

print(f"C_geom      = {C_geom}")
print(f"c_plateau   = {c_plateau}")
print(f"K_xi        = {K_xi}")
print(f"Upsilon     = {Upsilon:.6f}")
print(f"Upsilon < 0.5? {'YES' if Upsilon < 0.5 else 'NO'}")
