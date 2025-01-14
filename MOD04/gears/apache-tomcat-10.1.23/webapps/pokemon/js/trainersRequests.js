
let tableContainerId = 'table';
let detailsContainerId = 'details';
let trainers = {};
let selectedTrainer = {};
let baseTrainer = {
    "name": null,
    "profileUrl": null
};
let defaultTrainer = {
    "name": "Ash Ketchum",
    "id": 1,
    "profileUrl": "https://archives.bulbagarden.net/media/upload/thumb/c/cd/Ash_JN.png/300px-Ash_JN.png"
}

function changeSelectedTrainer(id) {
    selectedTrainer = trainers?.data?.find(pt => pt.id === id);
    showDetails();
}

function showDetails() {
    const detailsContainer = document.getElementById(detailsContainerId);

    detailsContainer.innerHTML = `
    <div class="card" id="${selectedTrainer.id}_card">
      <img src="${selectedTrainer.profileUrl}" class="card-img-top">
      <div class="card-body">
        <h5 class="card-title">${selectedTrainer.name} (${selectedTrainer.id})</h5>
      </div>
      
      <ul class="list-group list-group-flush">
            <li class="list-group-item">
                <span class="font-weight-bold">ID:</span> ${selectedTrainer.id}
            </li>
            <li class="list-group-item">
                <span class="font-weight-bold">Created:</span> ${selectedTrainer.created}
            </li>
            <li class="list-group-item">
                <span class="font-weight-bold">Last update:</span> ${selectedTrainer.lastUpDate}
            </li>
            <li class="list-group-item">
                <span class="font-weight-bold">Name:</span> ${selectedTrainer.name}
            </li>
            <li class="list-group-item">
                <span class="font-weight-bold">Image URL:</span> ${selectedTrainer.profileUrl}
            </li>
            <li class="list-group-item d-flex justify-content-between">
                <a class="btn btn-primary" onclick="showCreateForm()">New</a>
                <a class="btn btn-primary" onclick="showUpdateForm()">Update</a>
                <a class="btn btn-danger" onclick="deleteTrainer(selectedTrainer.id)">Delete</a>
            </li>
      </ul>
    </div>
    `
}


function createTrainersTable() {
    const tableContainer = document.getElementById(tableContainerId);
    tableContainer.innerHTML = `
        <table class="table table-striped table-hover">
            <thead>
                <tr>
                    <th scope="col">ID</th>
                    <th scope="col">Name</th>
                </tr>
            </thead>
            <tbody>
                ${
                    trainers.data.map(resource => `${trainerToRow(resource)}`).join("\n")
                    || "no data"
                }
            </tbody>
        </table>
    `

    if(trainers?.data?.[0]?.id)
        changeSelectedTrainer(trainers?.data?.[0]?.id)
}

function trainerToRow(trainer) {
    return `
    <tr id="${trainer.id}_row" onclick="changeSelectedTrainer('${trainer?.id?.trim()}')">
        <th scope="row">${trainer.id}</th>
        <td>${trainer.name}</td>
    </tr>
    `
}

function getTrainers() {
    return fetch('./api/trainers')
        .then(res => res.json())
        .then(data => {
            trainers = data;
            createTrainersTable();
        })
        .catch(err => {
            console.error(`Unable to fetch trainers: ${err.status}`);
            console.error(err);
        });
}

function deleteTrainer(id) {
    return fetch(`./api/trainers/${id}`, { method: "DELETE" })
        .then(() => {
            getTrainers()
        })
        .catch(err => {
            console.error(`Unable to delete trainer: ${err.status}`);
            console.error(err);
        });
}


function showUpdateForm() {
    const detailsContainer = document.getElementById(detailsContainerId);

    detailsContainer.innerHTML = `
    <form id="update-form">
          <div class="form-group">
                <label for="input-name">Name</label>
                <input type="text" class="form-control" id="input-name" name="name" placeholder="${selectedTrainer.name}">
          </div>
          <div class="form-group">
                <label for="input-profile-url">Profile URL</label>
                <input type="text" class="form-control" id="input-profile-url" name="profileUrl" placeholder="${selectedTrainer.profileUrl}">
          </div>
          <div class="d-flex justify-content-between">
                <button type="submit" class="btn btn-primary">Submit</button>
                <button type="button" class="btn btn-danger" onclick="showDetails()">Cancel</button>
          </div>
    </form>
    `

    const form = document.getElementById("update-form");
    form.addEventListener("submit", function(event) {
            event.preventDefault();

            let formData = new FormData(form);
            formData.forEach((v,k) => {
                selectedTrainer[k] = formData.get(k) || selectedTrainer[k];
            })

            const id = selectedTrainer.id;
            fetch(`./api/trainers/${id}`, {
                    method: "PUT",
                    headers: { "Content-Type": "application/json" },
                    body: JSON.stringify(selectedTrainer, null, 2)
                }).then(res => getTrainers())
                .then(() => changeSelectedTrainer(id))
                .catch(err => {
                    console.error("Error updating resource", err)
                })
        })
}

function showCreateForm() {
    const detailsContainer = document.getElementById(detailsContainerId);

    detailsContainer.innerHTML = `
    <form id="create-form">
          <div class="form-group">
                <label for="input-name">Name</label>
                <input type="text" class="form-control" id="input-name" name="name" placeholder="${defaultTrainer.name}">
          </div>
          <div class="form-group">
                <label for="input-profile-url">Profile URL</label>
                <input type="text" class="form-control" id="input-profile-url" name="profileUrl" placeholder="${defaultTrainer.profileUrl}">
          </div>
          <div class="d-flex justify-content-between">
                <button type="submit" class="btn btn-primary">Submit</button>
                <button type="button" class="btn btn-danger" onclick="showDetails()">Cancel</button>
          </div>
    </form>
    `

    const form = document.getElementById("create-form");
    form.addEventListener("submit", function(event) {
            event.preventDefault();

            let newTrainer = JSON.parse(JSON.stringify(baseTrainer));
            let formData = new FormData(form);
            formData.forEach((v,k) => {
                newTrainer[k] = formData.get(k);
            })

            let newId;
            fetch(`./api/trainers`, {
                    method: "POST",
                    headers: { "Content-Type": "application/json" },
                    body: JSON.stringify(newTrainer, null, 2)
                }).then(res => res.json())
                .then(data => {
                    newId = data.id;
                    return getTrainers();
                })
                .then(() => changeSelectedTrainer(newId))
                .catch(err => {
                    console.error("Error updating resource", err)
                })
        })
}
