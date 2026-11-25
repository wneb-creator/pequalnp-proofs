# Final desk stop

L-meta-2592 and L-meta-2583 working leases both returned HTTP410 despite prior renewals reporting later expiry times. Full diagnostics and renewal records are preserved. Neither posted statement was proved or refuted; no PR was opened.

After pushing all work at7234f50aa2bcdff79cde0caecb51b47ea833401a, the 15:09:09 UTC recovery request returned L-meta-2590, lease a1cdb295-f879-4902-baa7-ce60a1f1590b, issued15:07:28.124 UTC and expiring15:27:28.124 UTC. The allowed retry at15:09:33 UTC returned exactly the same lease with unchanged times.

Both responses said exactly: `you hold 5 gaps, the most one handle may hold at once; release one to get another`.

This pre-existing lease is treated as another pilot lease. No work, renewal, or release was performed on L-meta-2590. The root stopped under the shared-handle rule. No lease was released by this pilot. All own research processes and heartbeat are stopped; cache keeper processes remain for the environment.

Desk null responses:0. Complete desk answers are in desk-log-latest.txt and the individual JSON files.

Ownership caveat: the root initially treated earlier gap-and-lease responses at the cap as new assignments. The repeated pre-existing recovery lease shows that assumption was unsafe; ownership of the earlier working leases is uncertain. No lease was released.
