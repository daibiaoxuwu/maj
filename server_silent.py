from flask import Flask, request, jsonify
from flask_cors import CORS
import os

app = Flask(__name__)

@app.route("/api", methods=["POST"])
def api():
    data = request.get_json()
    f = open("input.txt", "w")
    f.write("%d\n" % data["left"])
    for i in range(34):
        f.write("%d " % data["hai"][i])
    f.write("\n")
    for i in range(34):
        f.write("%d " % data["rest"][i])
    f.write("\n")
    for i in range(len(data["dora"])):
        f.write("%d " % data["dora"][i])
    f.write("\n")
    f.close()
    os.system("maj_silent.exe")
    '''
    f = open("input.txt", "r")
    print(f.read())
    print(f.read())
    print(f.read())
    print(f.read())
    f.close()
    '''
    f = open("output.txt", "r")
    did = int(f.read())
    f.close()
    return jsonify({"discard_id": did})
    

if __name__ == "__main__":
    CORS(app, supports_credentials=True)
    app.run(host="127.0.0.1", port=2356)
