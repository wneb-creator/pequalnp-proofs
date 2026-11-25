# Timeline

- 2026-11-25 15:39:27UTC: desk returned L4970 after3nullqueue replies; initially mistaken for a fresh allocation.
- 2026-11-25 approximately15:53UTC: independently reviewed checked helpers pushed at6d454fbc10c0a95eab39c4938a17aebec52587e5.
- 2026-11-25 approximately15:57UTC: ownership audit found issued_at15:22 predates the request, with the five-gap limit note. Work and renewal stopped; one retry returned the same existing lease. No lease was released.
- Final state: no full proof, no refutation, no PR; all partial results preserved.
