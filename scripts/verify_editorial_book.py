from pathlib import Path
import sys
sys.path.insert(0,'/home/lucas/Projects/scripts')
from verify_document import build_book
errors=build_book(Path('notes/latex'),'main.tex')
for e in errors: print(e)
raise SystemExit(bool(errors))
