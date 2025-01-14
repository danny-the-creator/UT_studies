import os
import importlib.util
import sys

class Tester:
    def __init__(self, assignment_id: int, student_number: int):
        module_name = f"assignment_{assignment_id}"
        self.student_number = student_number

        # Initialize module_path to None
        module_path = None

        # Define the starting points for the search
        search_start_dirs = [os.getcwd(), os.path.dirname(__file__)]

        # Search for the module file in the directory tree
        for start_dir in search_start_dirs:
            for root, dirs, files in os.walk(start_dir):
                if f"{module_name}.py" in files:
                    module_path = os.path.join(root, f"{module_name}.py")
                    break  # Module found
            if module_path:
                break  # No need to search further

        if not module_path:
            raise FileNotFoundError(f"Cannot find module file {module_name}.py")

        # Add the module's directory to sys.path if necessary
        module_dir = os.path.dirname(module_path)
        if module_dir not in sys.path:
            sys.path.append(module_dir)

        # Load the module
        spec = importlib.util.spec_from_file_location(module_name, module_path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)

        # Instantiate the Assignment class from the module
        self.assignment = getattr(module, "Assignment")()

    def test(self, function, *args):
        test_method_name = f'test_{function.__name__}'
        print(test_method_name)
        # You can add a logging statement here if desired

        try:
            test_method = getattr(self.assignment, test_method_name)
            # Pass the function itself along with other arguments
            test_method(function, *args)
            print(f"Passed! Test for function '{function.__name__}' passed.")
        except AttributeError:
            print(f"No test method found for: {function.__name__}")
        except Exception as e:
            print(f"Error in function '{function.__name__}': \n\t{e}")
