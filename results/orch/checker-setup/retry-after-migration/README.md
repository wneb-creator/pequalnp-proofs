# Official checker retry after cache migration

The unchanged official checker was retried on the same frozen 1,148-line L-meta-4970 partial after the parent renewed its lease. The source hash, statement hash, exact command, complete stdout/stderr/driver logs, external-guard result, and periodic memory samples are preserved here.

The checker again reached no verdict. It exited 3 after 216.97 seconds, with the wrapper reporting that the native verifier ended without a verdict (exit null). The same external guard stopped the process group when non-reclaimable memory reached 7,791,775,744 bytes, above its 7.25 GiB threshold. The cgroup OOM and OOM-kill counters remained zero. Periodic samples missed the final abrupt rise; the guard sampled every0.2 seconds and captured the peak.

No checker acceptance or mathematical rejection is claimed. The partial has no final target theorem; a completed checker run was expected to reject that absence. Genuine cache migration and the unchanged cached native-checker build passed their separate validations, but this full-checker capacity test still failed to reach a verdict. No subsequent retry was started at this checkpoint.
