#!/usr/bin/env python
try:
    from setuptools import setup
except ImportError:
    from distutils.core import setup

# Allow trove classifiers in previous python versions
from sys import version
if version < '2.2.3':
    from distutils.dist import DistributionMetadata
    DistributionMetadata.classifiers = None
    DistributionMetadata.download_url = None

from protocheck import __version__ as version

def requireModules(moduleNames=None):
    import re
    if moduleNames is None:
        moduleNames = []
    else:
        moduleNames = moduleNames

    commentPattern = re.compile(r'^\w*?#')
    moduleNames.extend(
        filter(lambda line: not commentPattern.match(line), 
            open('requirements.txt').readlines()))

    return moduleNames


entry_points = {
    'console_scripts': ['bspl = protocheck.bspl:main'],
}

setup(
    name='protocheck',
    version=version,

    author='Samuel Christie',
    author_email='schrist@ncsu.edu',

    description='Protocol verification tool for BSPL',
    long_description=open('README.org').read(),
    classifiers=[
        'Development Status :: 2 - Pre-Alpha',
        'Intended Audience :: Developers'
    ],

    entry_points=entry_points,

    install_requires=requireModules(),

    test_suite='protocheck'
)
