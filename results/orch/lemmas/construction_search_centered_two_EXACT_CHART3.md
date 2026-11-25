# Exact standalone certificate for mixed chart3

This is an exact algebra certificate, not a Lean proof and not a global centered-two-plane exclusion.

For the mixed physical chart(a,e)=(x,y), the CRT reconstruction finished after61primes, giving a positive890-bit integer N and3578nonzero integer row weights. Their weighted polynomial sum is exactly N. Each row is a monomial multiple of one of the twelve centered-plane equations; the final equation has zero multiplier. The largest coefficient has900bits. Thus these chart equations cannot all vanish over a characteristic-zero field.

The CRT code first verified the full integer matrix identity after clearing denominators. A separate verifier then checked directly against the original .msolve equations and row-origin metadata, without using the generated matrix. It also independently recomputed trace(B²), permanent(B), and permanent(H diag(0,B) H/4) for the chart and confirmed the input equations. The three_plane_search agent independently inspected and reran that verifier; both checks passed. The corresponding logs and verification JSON are included.

Restore original filenames by removing the archive prefix and run `centered_two_verify_exact.py 3` with the previously archived chart3 .msolve input and degree-nine metadata. The certificate JSON is about1MiB, so it cannot be copied literally into a proof file under the repository's512KiB source cap. A Lean proof would require compression, an algorithmic derivation, or a different proof strategy. Mixed chart2 remains a separate obligation; its CRT reconstruction is still in progress at this preservation point.
