// Danil Badarev s3210928
// Alexandr Gidikov s3200205
function onrequest(req) {
  // This function will be called everytime the browser is about to send out an http or https request.
  // The req variable contains all information about the request.
  // If we return  {} the request will be performed, without any further changes
  // If we return  {cancel:true}, the request will be cancelled.
  // If we return  {requestHeaders:req.requestHeaders}, any modifications made to the requestHeaders (see below) are sent.
    if (req.type=="beacon" || req.type == "xmlhttprequest"){// cancel the request if it is an add
                                                // or if it sends information to other sites
        return {cancel:true}
    }
    // let's do something special if an image is loaded:
    if (req.type=="image") {
        console.log("Ooh, it's a picture!");
        if (req.url.naturalHeight<=1 || req.url.naturalWidth<=1){
            // checks if the size of the picture is mover than 1 px
            return {cancel: true}
        }
    }
    let i;
    for (i=0; i< req.requestHeaders.length; i++) {
        // Hides user-agent and disables cookies
        if (req.requestHeaders[i].name === "User-Agent" || req.requestHeaders[i].name === "Cookie"){
            req.requestHeaders[i].value = "privacy!!11!";
        }
    }
  // log what file we're going to fetch:
  console.log("Loading: " + req.method +" "+ req.url + " "+ req.type);
  console.log(req.requestHeaders)



  // req also contains an array called requestHeaders containing the name and value of each header.
  // You can access the name and value of the i'th header as req.requestHeaders[i].name and req.requestHeaders[i].value,
  // with i from 0 up to (but not including!) req.requestHeaders.length

  return {requestHeaders:req.requestHeaders};
}


// no need to change the following! This just makes sure that the above function is called whenever the browser wants to fetch a file
browser.webRequest.onBeforeSendHeaders.addListener(
  onrequest,
  {urls: ["<all_urls>"]},
  ["blocking", "requestHeaders"]
);

