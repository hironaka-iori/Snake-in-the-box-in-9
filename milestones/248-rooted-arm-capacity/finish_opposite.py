"""Continue only unfinished opposite-end searches with a larger per-parent allowance."""
import sys
from opposite import main

if __name__ == "__main__":
    sys.argv = [sys.argv[0],"--seconds","28","--child-seconds","14","--parent-seconds","112"]
    main()
