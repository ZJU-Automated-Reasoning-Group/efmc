import os
import subprocess
import tempfile
from flask import Flask, render_template, request, jsonify, send_from_directory
from werkzeug.utils import secure_filename

app = Flask(__name__)
app.config['UPLOAD_FOLDER'] = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'uploads')
app.config['MAX_CONTENT_LENGTH'] = 16 * 1024 * 1024  # 16MB max upload size
app.config['EXAMPLES_FOLDER'] = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'data')
app.config['DEFAULT_TIMEOUT'] = 60  # Default timeout in seconds

# Create upload folder if it doesn't exist
os.makedirs(app.config['UPLOAD_FOLDER'], exist_ok=True)

# Allowed file extensions
ALLOWED_EXTENSIONS = {'smt2', 'sl', 'chc', 'sygus'}

def allowed_file(filename):
    return '.' in filename and filename.rsplit('.', 1)[1].lower() in ALLOWED_EXTENSIONS

@app.route('/')
def index():
    return render_template('index.html')

@app.route('/efmc')
def efmc_page():
    return render_template('efmc.html')

@app.route('/efsmt')
def efsmt_page():
    return render_template('efsmt.html')

@app.route('/about')
def about_page():
    return render_template('about.html')

@app.route('/api/run_efmc', methods=['POST'])
def run_efmc():
    if 'file' not in request.files and 'code' not in request.form:
        return jsonify({'error': 'No file or code provided'}), 400
    
    engine = request.form.get('engine', 'ef')
    template = request.form.get('template', '')
    lang = request.form.get('lang', '')
    timeout = int(request.form.get('timeout', app.config['DEFAULT_TIMEOUT']))
    
    if 'file' in request.files and request.files['file'].filename:
        file = request.files['file']
        if not allowed_file(file.filename):
            return jsonify({'error': 'File type not allowed'}), 400
        
        filename = secure_filename(file.filename)
        filepath = os.path.join(app.config['UPLOAD_FOLDER'], filename)
        file.save(filepath)
    else:
        # Create a temporary file with the provided code
        code = request.form.get('code', '')
        with tempfile.NamedTemporaryFile(delete=False, suffix='.smt2') as tmp:
            tmp.write(code.encode())
            filepath = tmp.name
    
    # Build the command
    cmd = ['efmc', '--engine', engine]
    
    if template:
        cmd.extend(['--template', template])
    
    if lang:
        cmd.extend(['--lang', lang])
    
    cmd.extend(['--file', filepath])
    
    try:
        # Run the command and capture output
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        
        # Clean up temporary file if we created one
        if 'file' not in request.files or not request.files['file'].filename:
            os.unlink(filepath)
        
        return jsonify({
            'stdout': result.stdout,
            'stderr': result.stderr,
            'exit_code': result.returncode
        })
    except subprocess.TimeoutExpired:
        return jsonify({'error': f'Execution timed out ({timeout}s limit)'}), 408
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/api/run_efsmt', methods=['POST'])
def run_efsmt():
    if 'file' not in request.files and 'code' not in request.form:
        return jsonify({'error': 'No file or code provided'}), 400
    
    solver = request.form.get('solver', 'z3')
    timeout = int(request.form.get('timeout', app.config['DEFAULT_TIMEOUT']))
    
    if 'file' in request.files and request.files['file'].filename:
        file = request.files['file']
        if not allowed_file(file.filename):
            return jsonify({'error': 'File type not allowed'}), 400
        
        filename = secure_filename(file.filename)
        filepath = os.path.join(app.config['UPLOAD_FOLDER'], filename)
        file.save(filepath)
    else:
        # Create a temporary file with the provided code
        code = request.form.get('code', '')
        with tempfile.NamedTemporaryFile(delete=False, suffix='.smt2') as tmp:
            tmp.write(code.encode())
            filepath = tmp.name
    
    # Build the command (based on the error message, we need to specify the solver)
    cmd = ['efsmt', solver, '--file', filepath]
    
    # Add timeout if specified
    if timeout > 0:
        cmd.extend(['--timeout', str(timeout)])
    
    try:
        # Run the command and capture output
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        
        # Clean up temporary file if we created one
        if 'file' not in request.files or not request.files['file'].filename:
            os.unlink(filepath)
        
        return jsonify({
            'stdout': result.stdout,
            'stderr': result.stderr,
            'exit_code': result.returncode
        })
    except subprocess.TimeoutExpired:
        return jsonify({'error': f'Execution timed out ({timeout}s limit)'}), 408
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/api/examples', methods=['GET'])
def get_examples():
    examples = []
    for root, dirs, files in os.walk(app.config['EXAMPLES_FOLDER']):
        for file in files:
            if allowed_file(file):
                rel_path = os.path.relpath(os.path.join(root, file), app.config['EXAMPLES_FOLDER'])
                examples.append({
                    'path': rel_path,
                    'name': file
                })
    return jsonify(examples)

@app.route('/api/example/<path:filename>', methods=['GET'])
def get_example(filename):
    return send_from_directory(app.config['EXAMPLES_FOLDER'], filename)

if __name__ == '__main__':
    app.run(debug=True, host='0.0.0.0', port=5050) 