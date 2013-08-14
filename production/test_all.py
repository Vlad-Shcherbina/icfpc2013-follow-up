import sys

import nose


if __name__ == '__main__':
    nose.run(argv=sys.argv + [
        '--verbose', '--with-doctest',
        #'--with-coverage', '--cover-package=production',
        '--logging-level=DEBUG'
        ])
