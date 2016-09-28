.PHONY: deps .venv

parser: precedence/bspl.gr
	cd precedence; grako -m Bspl bspl.gr >bspl_parser.py

activate: deps
	PYTHONPATH=.venv ; . .venv/bin/activate

.venv:
	if [ ! -e ".venv/bin/activate_this.py" ] ; then virtualenv --clear --python=python3.4 .venv ; fi
	. .venv/bin/activate && pip install --upgrade pip

deps: .venv requirements.txt
	PYTHONPATH=.venv ; . .venv/bin/activate && .venv/bin/pip install -U -r requirements.txt

test: .venv setup.py
	PYTHONPATH=.venv ; . .venv/bin/activate && .venv/bin/python setup.py test

clean:
	rm -rf .venv build *.egg-info
	rm -f `find . -name \*.pyc -print0 | xargs -0`
