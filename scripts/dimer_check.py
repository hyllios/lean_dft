"""Numerical reality check of LatticeDFT/TDDFT/Dimer.lean.

Integrate i psi' = (-T sigma_x + diag(v0, v1)) psi for a driven dimer, keep only the density
n0(t), and reconstruct the potential difference from the closed form of `dimer_td_potential`:
    (v0 - v1)^2 (4 T^2 n0 n1 - n0'^2) = (n0'' + 2 T^2 (n0 - n1))^2,
with the sign fixed by the bond order b = Re(conj(psi0) psi1) (`ddens_dimer`):
    v0 - v1 = -(n0'' + 2 T^2 (n0 - n1)) / (2 T b).
Also checks the speed limit n0'^2 <= 4 T^2 n0 n1 and the Rabi oscillation (b = 0 throughout).
"""
import numpy as np
from scipy.integrate import solve_ivp

T = 1.0
dv = lambda t: 1.5 * np.sin(1.3 * t) + 0.4  # driving potential difference v0 - v1


def rhs(t, y):
    psi = y[:2] + 1j * y[2:]
    H = np.array([[dv(t) / 2, -T], [-T, -dv(t) / 2]])
    d = -1j * H @ psi
    return np.concatenate([d.real, d.imag])


# start from the ground state of the t = 0 Hamiltonian
H0 = np.array([[dv(0) / 2, -T], [-T, -dv(0) / 2]])
w, U = np.linalg.eigh(H0)
psi0 = U[:, 0]
ts = np.linspace(0, 6, 6001)
sol = solve_ivp(rhs, (0, 6), np.concatenate([psi0.real, psi0.imag]), t_eval=ts,
                rtol=1e-12, atol=1e-12)
psi = sol.y[:2] + 1j * sol.y[2:]
n0, n1 = abs(psi[0]) ** 2, abs(psi[1]) ** 2
b = (np.conj(psi[0]) * psi[1]).real
h = ts[1] - ts[0]
n0d = np.gradient(n0, h, edge_order=2)
n0dd = np.gradient(n0d, h, edge_order=2)
dv_rec = -(n0dd + 2 * T**2 * (n0 - n1)) / (2 * T * b)
inner = slice(10, -10)
print("min bond order b           :", b.min())
print("max |v0-v1 reconstructed - true|:", np.max(abs(dv_rec - dv(ts))[inner]))
gap = 4 * T**2 * n0 * n1 - n0d**2
print("min speed-limit gap 4T^2 n0 n1 - n0'^2:", gap[inner].min(), "(b^2*4T^2 min:",
      (4 * T**2 * b**2).min(), ")")
sq = dv(ts) ** 2 * gap - (n0dd + 2 * T**2 * (n0 - n1)) ** 2
print("max |closed-form residual| :", np.max(abs(sq[inner])))

# Rabi oscillation: psi = (cos Tt, i sin Tt), no potential
r0, r1 = np.cos(T * ts), 1j * np.sin(T * ts)
print("Rabi: max |b| =", np.max(abs((np.conj(r0) * r1).real)),
      " max |n0'^2 - 4T^2 n0 n1| =",
      np.max(abs((-T * np.sin(2 * T * ts)) ** 2 - 4 * T**2 * abs(r0)**2 * abs(r1)**2)))
